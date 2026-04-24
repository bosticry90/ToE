from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_limitation_characterization_packet_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_limitation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_review_20260412_v0.json",
                "bridge_probe_significance_adjudication_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "limitation_class_policy": {
                "admitted_classes": [
                    "signal_stability_limitation",
                    "comparator_bound_limitation",
                    "robustness_margin_limitation",
                    "probe_sensitivity_limitation",
                ],
                "single_dominant_class_required": True,
                "external_path_success_signal_margin_min": 0.05,
                "no_promotion_claim": True,
                "no_seam_closure": True,
            },
            "packet_contract": {
                "allowed_outcomes": [
                    "COMPARATOR_BOUND_LIMITATION_CONFIRMED",
                    "SIGNAL_STABILITY_LIMITATION_CONFIRMED",
                    "ROBUSTNESS_MARGIN_LIMITATION_CONFIRMED",
                    "PROBE_SENSITIVITY_LIMITATION_CONFIRMED",
                    "LIMITATION_CLASS_INDETERMINATE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_LIMITATION_CHARACTERIZATION_OUTCOME",
                "no_loop_rule": "ONE_LIMITATION_CHARACTERIZATION_PACKET_ONLY",
                "default_outcome": "COMPARATOR_BOUND_LIMITATION_CONFIRMED",
                "stop_after": "EXECUTION_RULING_FOCUSED_GATES_REFRESHED_TOKEN_READ",
            },
        },
    )


def _seed_limitation_review(
    root: Path,
    *,
    review_outcome: str = "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD",
    limitation_primary_cause: str = "comparator_repeatability_or_cross_probe_consistency_not_yet_confirmed",
    local_and_refinable: bool = True,
    signal_margin: float = 0.04,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "local_and_refinable": local_and_refinable,
                "one_more_bounded_comparator_cycle_justified": False,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": signal_margin,
                "next_action": "KEEP_SEAM_ACTIVE_AS_LIMITED_AND_PREPARE_BOUNDED_LIMITATION_HARDENING",
            }
        },
    )


def _seed_significance(
    root: Path,
    *,
    adjudication_outcome: str = "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
    comparator_repeatability_confirmed: bool = False,
    cross_probe_consistency_confirmed: bool = False,
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260412_v0.json",
        {
            "summary": {
                "adjudication_outcome": adjudication_outcome,
            },
            "objective_quality": {
                "inputs": {
                    "external_path_success_signal_margin_min": 0.05,
                    "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                    "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                }
            },
        },
    )


def test_characterization_packet_comparator_bound_is_dominant(
    tmp_path: Path, monkeypatch
) -> None:
    """The canonical current state: comparator-bound is the dominant limiting factor."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path)
    _seed_significance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["packet_outcome"] == "COMPARATOR_BOUND_LIMITATION_CONFIRMED"
    assert report["summary"]["dominant_limitation_class"] == "comparator_bound_limitation"
    assert report["summary"]["signal_margin"] == pytest.approx(0.04, abs=1e-9)
    assert report["summary"]["signal_margin_gap_below_threshold"] == pytest.approx(0.01, abs=1e-9)
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    assert report["summary"]["next_action"] == "KEEP_BRIDGE_SEAM_PRIMARY_WITH_BOUNDED_LIMITATION_DISCIPLINE"
    assert report["objective_quality"]["summary"]["all_criteria_satisfied"] is True
    assert report["criteria"]["significance_outcome_is_probe_signal_confirmed_but_limited"] is True
    assert report["criteria"]["single_dominant_class_resolved"] is True


def test_characterization_packet_signal_stability_when_one_more_cycle(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(
        tmp_path,
        review_outcome="LIMITATION_LOCAL_REFINABLE_ONE_MORE_BOUNDED_COMPARATOR_CYCLE_JUSTIFIED",
        limitation_primary_cause="local_signal_discrimination_insufficient",
    )
    _seed_significance(tmp_path, adjudication_outcome="PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["packet_outcome"] == "SIGNAL_STABILITY_LIMITATION_CONFIRMED"
    assert report["summary"]["dominant_limitation_class"] == "signal_stability_limitation"


def test_characterization_packet_robustness_margin_when_margin_hold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(
        tmp_path,
        review_outcome="LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
        limitation_primary_cause="signal_margin_below_external_path_success_threshold",
    )
    _seed_significance(
        tmp_path,
        comparator_repeatability_confirmed=True,
        cross_probe_consistency_confirmed=True,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["packet_outcome"] == "ROBUSTNESS_MARGIN_LIMITATION_CONFIRMED"
    assert report["summary"]["dominant_limitation_class"] == "robustness_margin_limitation"


def test_characterization_packet_probe_sensitivity_when_scope_hold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(
        tmp_path,
        review_outcome="LIMITATION_INTERPRETATION_SCOPE_HOLD",
        limitation_primary_cause="interpretation_scope_or_path_validity_not_sufficient_for_advancement",
    )
    _seed_significance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["packet_outcome"] == "PROBE_SENSITIVITY_LIMITATION_CONFIRMED"
    assert report["summary"]["dominant_limitation_class"] == "probe_sensitivity_limitation"


def test_characterization_packet_enforces_no_promotion_no_closure(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path)
    _seed_significance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    # next_action must not contain promotion or closure language
    next_action = report["summary"]["next_action"]
    assert "PROMOTION" not in next_action
    assert "CLOSURE" not in next_action
