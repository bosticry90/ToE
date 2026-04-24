from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_signal_margin_hardening_cycle_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_20260422_v0.json",
                "bridge_limitation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v2.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "acceptance_policy": {
                "required_cycle_outcome": "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD",
                "required_limitation_outcome": "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
                "required_limitation_primary_cause": "signal_margin_below_external_path_success_threshold",
                "allow_acceptance_at_current_margin_ceiling": True,
                "not_a_multi_cycle": True,
                "no_scope_expansion": True,
                "margin_ceiling_tolerance": 1e-9,
            },
            "acceptance_contract": {
                "allowed_outcomes": [
                    "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING",
                    "SIGNAL_MARGIN_LIMITATION_NOT_ACCEPTED_CONTINUE_BOUNDED_HARDENING",
                    "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED",
                    "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_OUTCOME",
                "no_loop_rule": "ONE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_ONLY",
                "default_outcome": "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED",
            },
        },
    )


def _seed_cycle_report(
    root: Path,
    *,
    cycle_outcome: str = "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD",
    signal_margin: float = 0.05,
    success_margin_min: float = 0.05,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_20260422_v0.json",
        {
            "summary": {
                "cycle_outcome": cycle_outcome,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {
                "inputs": {
                    "post_signal_margin": signal_margin,
                    "success_margin_min": success_margin_min,
                }
            },
        },
    )


def _seed_limitation_report(
    root: Path,
    *,
    review_outcome: str = "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
    limitation_primary_cause: str = "signal_margin_below_external_path_success_threshold",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v2.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {"inputs": {}},
        },
    )


def test_accepts_margin_limited_state_at_current_ceiling(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path, signal_margin=0.05, success_margin_min=0.05)
    _seed_limitation_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING"
    assert report["summary"]["accepted_as_margin_limited"] is True


def test_not_accepted_when_gap_remains_above_tolerance(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path, signal_margin=0.045, success_margin_min=0.05)
    _seed_limitation_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["review_outcome"]
        == "SIGNAL_MARGIN_LIMITATION_NOT_ACCEPTED_CONTINUE_BOUNDED_HARDENING"
    )
    assert report["summary"]["accepted_as_margin_limited"] is False


def test_precondition_failed_when_limitation_outcome_not_signal_hold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path)
    _seed_limitation_report(tmp_path, review_outcome="LIMITATION_INTERPRETATION_SCOPE_HOLD")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED"
    assert report["criteria"]["limitation_outcome_matches_required"] is False


def test_scope_violation_when_declared_and_observed_scope_mismatch(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path, comparator_id="OV-RL-10-ALT")
    _seed_limitation_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_acceptance_always_preserves_non_promotion_non_closure_guards(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path)
    _seed_limitation_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    assert "PROMOTION" not in report["summary"]["next_action"]
    assert "CLOSURE" not in report["summary"]["next_action"]
