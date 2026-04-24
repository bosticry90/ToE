from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_comparator_repeatability_confirmation_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    window_check_executed: bool = False,
    window_check_comparator_stable: bool = False,
    window_check_within_admissible_scope: bool = True,
    not_a_full_second_cycle: bool = True,
    no_scope_expansion: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_limitation_characterization_packet_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_characterization_packet_20260422_v0.json",
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
                "bridge_material_repeatability_admissibility_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "named_check_id": "rl10_bridge_sigma_db_repeatability_window_check_v0",
            },
            "confirmation_policy": {
                "required_limitation_class": "COMPARATOR_BOUND_LIMITATION_CONFIRMED",
                "required_naming_review_outcome": "BOUNDED_REPEATABILITY_CHECK_NAMED",
                "required_proposed_check_kind": "REPEATABILITY",
                "required_admissibility_criteria_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
                "window_check_executed": window_check_executed,
                "window_check_comparator_stable": window_check_comparator_stable,
                "window_check_within_admissible_scope": window_check_within_admissible_scope,
                "not_a_full_second_cycle": not_a_full_second_cycle,
                "no_scope_expansion": no_scope_expansion,
                "signal_margin_gap_targeted": 0.01,
                "signal_margin_threshold": 0.05,
            },
            "confirmation_contract": {
                "allowed_outcomes": [
                    "COMPARATOR_REPEATABILITY_CONFIRMED",
                    "COMPARATOR_REPEATABILITY_NOT_YET_CONFIRMED",
                    "WINDOW_CHECK_SCOPE_VIOLATION",
                    "ADMISSIBILITY_PRECONDITION_FAILED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_COMPARATOR_REPEATABILITY_CONFIRMATION_OUTCOME",
                "no_loop_rule": "ONE_COMPARATOR_REPEATABILITY_CONFIRMATION_ONLY",
                "default_outcome": "COMPARATOR_REPEATABILITY_NOT_YET_CONFIRMED",
                "stop_after": "EXECUTION_RULING_FOCUSED_GATES_REFRESHED_TOKEN_READ",
            },
        },
    )


def _seed_char_packet(root: Path, *, packet_outcome: str = "COMPARATOR_BOUND_LIMITATION_CONFIRMED") -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_characterization_packet_20260422_v0.json",
        {
            "summary": {
                "packet_outcome": packet_outcome,
                "dominant_limitation_class": "comparator_bound_limitation",
                "signal_margin": 0.04,
                "signal_margin_gap_below_threshold": 0.01,
                "no_promotion_claim": True,
                "no_seam_closure": True,
                "next_action": "KEEP_BRIDGE_SEAM_PRIMARY_WITH_BOUNDED_LIMITATION_DISCIPLINE",
            }
        },
    )


def _seed_naming_review(
    root: Path,
    *,
    review_outcome: str = "BOUNDED_REPEATABILITY_CHECK_NAMED",
    proposed_check_kind: str = "REPEATABILITY",
    proposed_check_name: str = "rl10_bridge_sigma_db_repeatability_window_check_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "proposed_check_kind": proposed_check_kind,
                "proposed_check_name": proposed_check_name,
                "named_check_admissible": True,
                "next_action": "PREPARE_ONE_BOUNDED_REPEATABILITY_CHECK_PACKET",
            }
        },
    )


def _seed_admissibility(
    root: Path,
    *,
    terminal_outcome: str = "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": terminal_outcome,
                "repeatability_admissibility_criteria_defined": True,
                "criteria_nonexpansive": True,
                "criteria_scoped_to_named_check": True,
            }
        },
    )


def test_confirmation_reports_not_yet_confirmed_when_window_check_not_executed(
    tmp_path: Path, monkeypatch
) -> None:
    """Canonical current state: check is named and admissible but window not yet executed."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_char_packet(tmp_path)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["confirmation_outcome"] == "COMPARATOR_REPEATABILITY_NOT_YET_CONFIRMED"
    assert report["summary"]["repeatability_confirmed"] is False
    assert (
        report["summary"]["next_action"]
        == "EXECUTE_ONE_BOUNDED_WINDOW_CHECK_AGAINST_NAMED_REPEATABILITY_CHECK_ID"
    )
    assert report["summary"]["named_check_id"] == "rl10_bridge_sigma_db_repeatability_window_check_v0"
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    assert report["criteria"]["limitation_class_is_comparator_bound"] is True
    assert report["criteria"]["naming_review_outcome_is_bounded_check_named"] is True
    assert report["criteria"]["admissibility_criteria_declared"] is True
    assert report["criteria"]["scope_guards_satisfied"] is True
    assert report["objective_quality"]["criteria"]["admissibility_preconditions_satisfied"] is True


def test_confirmation_reports_confirmed_when_window_check_executed_and_stable(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(
        declaration_path,
        window_check_executed=True,
        window_check_comparator_stable=True,
    )
    _seed_char_packet(tmp_path)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["confirmation_outcome"] == "COMPARATOR_REPEATABILITY_CONFIRMED"
    assert report["summary"]["repeatability_confirmed"] is True


def test_confirmation_reports_scope_violation_when_not_admissible(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(
        declaration_path,
        window_check_within_admissible_scope=False,
    )
    _seed_char_packet(tmp_path)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["confirmation_outcome"] == "WINDOW_CHECK_SCOPE_VIOLATION"
    assert report["summary"]["repeatability_confirmed"] is False


def test_confirmation_reports_precondition_failed_when_limitation_class_wrong(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_char_packet(tmp_path, packet_outcome="SIGNAL_STABILITY_LIMITATION_CONFIRMED")
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["confirmation_outcome"] == "ADMISSIBILITY_PRECONDITION_FAILED"
    assert report["criteria"]["limitation_class_is_comparator_bound"] is False


def test_confirmation_enforces_no_promotion_no_closure_always(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_char_packet(tmp_path)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    next_action = report["summary"]["next_action"]
    assert "PROMOTION" not in next_action
    assert "CLOSURE" not in next_action
    assert report["summary"]["signal_margin_gap_targeted"] == pytest.approx(0.01, abs=1e-9)
    assert report["summary"]["signal_margin_threshold"] == pytest.approx(0.05, abs=1e-9)
