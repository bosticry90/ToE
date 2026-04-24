from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_significance_inputs_refresh_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_probe_significance_adjudication_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260412_v0.json",
                "bridge_comparator_repeatability_confirmation_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_comparator_repeatability_confirmation_20260422_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "refresh_policy": {
                "required_significance_outcome": "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
                "required_repeatability_confirmation_outcome": "COMPARATOR_REPEATABILITY_CONFIRMED",
                "cross_probe_consistency_confirmed": False,
                "not_a_new_adjudication_cycle": True,
                "no_scope_expansion": True,
            },
            "refresh_contract": {
                "allowed_outcomes": [
                    "SIGNIFICANCE_INPUTS_REFRESHED",
                    "SIGNIFICANCE_INPUTS_UNCHANGED",
                    "SIGNIFICANCE_INPUTS_REFRESH_PRECONDITION_FAILED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SIGNIFICANCE_INPUTS_REFRESH_OUTCOME",
                "no_loop_rule": "ONE_SIGNIFICANCE_INPUTS_REFRESH_ONLY",
                "default_outcome": "SIGNIFICANCE_INPUTS_UNCHANGED",
                "stop_after": "SIGNIFICANCE_INPUTS_REFRESH_RULING_LIMITATION_REVIEW_RERUN_TOKEN_READ",
            },
        },
    )


def _seed_significance_adjudication(
    root: Path,
    *,
    adjudication_outcome: str = "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
    comparator_repeatability_confirmed: bool = False,
    cross_probe_consistency_confirmed: bool = False,
    signal_margin: float = 0.04,
    external_path_success_signal_margin_min: float = 0.05,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
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
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": signal_margin,
            },
            "objective_quality": {
                "inputs": {
                    "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                    "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                    "signal_margin": signal_margin,
                    "external_path_success_signal_margin_min": external_path_success_signal_margin_min,
                    "confirmed_but_limited_signal_margin_min": 0.02,
                    "one_more_cycle_signal_margin_min": 0.0,
                    "expected_comparator_id": comparator_id,
                    "expected_quantity_id": quantity_id,
                }
            },
        },
    )


def _seed_confirmation_report(
    root: Path,
    *,
    confirmation_outcome: str = "COMPARATOR_REPEATABILITY_CONFIRMED",
    named_check_id: str = "rl10_bridge_sigma_db_repeatability_window_check_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_comparator_repeatability_confirmation_20260422_v0.json",
        {
            "summary": {
                "confirmation_outcome": confirmation_outcome,
                "named_check_id": named_check_id,
                "repeatability_confirmed": confirmation_outcome == "COMPARATOR_REPEATABILITY_CONFIRMED",
                "no_promotion_claim": True,
                "no_seam_closure": True,
            }
        },
    )


def test_significance_inputs_refreshed_when_repeatability_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    """Canonical case: significance adjudication had comparator_repeatability=false, confirmation now confirms it."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_adjudication(tmp_path, comparator_repeatability_confirmed=False)
    _seed_confirmation_report(tmp_path, confirmation_outcome="COMPARATOR_REPEATABILITY_CONFIRMED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "SIGNIFICANCE_INPUTS_REFRESHED"
    assert report["summary"]["comparator_repeatability_confirmed_updated_to"] is True
    assert report["summary"]["inputs_changed"] is True
    assert report["summary"]["adjudication_outcome"] == "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED"
    assert report["objective_quality"]["inputs"]["comparator_repeatability_confirmed"] is True
    assert report["objective_quality"]["inputs"]["cross_probe_consistency_confirmed"] is False
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    assert report["objective_quality"]["criteria"]["preconditions_satisfied"] is True


def test_significance_inputs_unchanged_when_already_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    """If comparator_repeatability was already confirmed, refresh emits UNCHANGED."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_adjudication(tmp_path, comparator_repeatability_confirmed=True)
    _seed_confirmation_report(tmp_path, confirmation_outcome="COMPARATOR_REPEATABILITY_CONFIRMED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "SIGNIFICANCE_INPUTS_UNCHANGED"
    assert report["summary"]["inputs_changed"] is False
    assert report["objective_quality"]["inputs"]["comparator_repeatability_confirmed"] is True


def test_significance_inputs_precondition_failed_when_confirmation_not_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    """If confirmation outcome is not COMPARATOR_REPEATABILITY_CONFIRMED, precondition fails."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_adjudication(tmp_path, comparator_repeatability_confirmed=False)
    _seed_confirmation_report(
        tmp_path, confirmation_outcome="COMPARATOR_REPEATABILITY_NOT_YET_CONFIRMED"
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "SIGNIFICANCE_INPUTS_REFRESH_PRECONDITION_FAILED"
    assert report["summary"]["comparator_repeatability_confirmed_updated_to"] is False
    assert report["criteria"]["repeatability_confirmation_matches_required"] is False


def test_significance_inputs_precondition_failed_when_significance_outcome_wrong(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_adjudication(
        tmp_path,
        adjudication_outcome="WRONG_SIGNIFICANCE_OUTCOME",
        comparator_repeatability_confirmed=False,
    )
    _seed_confirmation_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "SIGNIFICANCE_INPUTS_REFRESH_PRECONDITION_FAILED"
    assert report["criteria"]["significance_outcome_matches_required"] is False


def test_significance_inputs_refresh_output_is_limitation_review_compatible(
    tmp_path: Path, monkeypatch
) -> None:
    """The refreshed output must have the fields the limitation review tool needs."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_adjudication(tmp_path, comparator_repeatability_confirmed=False)
    _seed_confirmation_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    # The limitation review tool reads these paths:
    # summary.adjudication_outcome
    assert "adjudication_outcome" in report["summary"]
    # objective_quality.inputs.comparator_repeatability_confirmed
    assert "comparator_repeatability_confirmed" in report["objective_quality"]["inputs"]
    # objective_quality.inputs.cross_probe_consistency_confirmed
    assert "cross_probe_consistency_confirmed" in report["objective_quality"]["inputs"]
    # objective_quality.inputs.external_path_success_signal_margin_min
    assert "external_path_success_signal_margin_min" in report["objective_quality"]["inputs"]
    assert report["objective_quality"]["inputs"]["external_path_success_signal_margin_min"] == pytest.approx(0.05)
    assert report["objective_quality"]["inputs"]["signal_margin"] == pytest.approx(0.04, abs=1e-9)
