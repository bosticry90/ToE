from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_interpretation_scope_reconciliation_review_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_probe_significance_adjudication_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260422_v1.json",
                "bridge_limitation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v2.json",
                "bridge_signal_margin_limitation_acceptance_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "reconciliation_policy": {
                "required_significance_outcome_for_external_success_candidate": "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE",
                "required_limitation_outcome_for_scope_hold": "LIMITATION_INTERPRETATION_SCOPE_HOLD",
                "required_acceptance_outcome_for_precondition_failure": "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED",
                "declaration_mapping_mismatch_if_external_success_and_scope_hold": True,
                "not_a_new_hardening_cycle": True,
                "no_scope_expansion": True,
            },
            "reconciliation_contract": {
                "allowed_outcomes": [
                    "INTERPRETATION_SCOPE_SHIFT_CONFIRMED_AS_CORRECT",
                    "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED",
                    "INTERPRETATION_SCOPE_RECONCILIATION_PRECONDITION_FAILED",
                    "INTERPRETATION_SCOPE_RECONCILIATION_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_RECONCILIATION_OUTCOME",
                "no_loop_rule": "ONE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_ONLY",
                "default_outcome": "INTERPRETATION_SCOPE_RECONCILIATION_PRECONDITION_FAILED",
            },
        },
    )


def _seed_significance(
    root: Path,
    *,
    outcome: str = "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260422_v1.json",
        {
            "summary": {
                "adjudication_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": 0.05,
            },
            "objective_quality": {
                "inputs": {
                    "external_path_success_signal_margin_min": 0.05,
                    "comparator_repeatability_confirmed": True,
                    "cross_probe_consistency_confirmed": True,
                }
            },
        },
    )


def _seed_limitation(
    root: Path,
    *,
    outcome: str = "LIMITATION_INTERPRETATION_SCOPE_HOLD",
    primary_cause: str = "interpretation_scope_or_path_validity_not_sufficient_for_advancement",
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
                "review_outcome": outcome,
                "limitation_primary_cause": primary_cause,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {"inputs": {}},
        },
    )


def _seed_acceptance(
    root: Path,
    *,
    outcome: str = "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": 0.05,
            }
        },
    )


def test_confirms_declaration_input_mismatch_when_external_success_and_scope_hold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path)
    _seed_acceptance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["review_outcome"]
        == "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED"
    )
    assert report["summary"]["reconciliation_status"] == "MAPPING_MISMATCH_CONFIRMED"


def test_confirms_shift_when_policy_disables_mismatch_rule(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["reconciliation_policy"]["declaration_mapping_mismatch_if_external_success_and_scope_hold"] = False
    _write_json(declaration_path, payload)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path)
    _seed_acceptance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_SHIFT_CONFIRMED_AS_CORRECT"


def test_precondition_failed_when_significance_outcome_not_external_success_candidate(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path, outcome="PROBE_SIGNAL_CONFIRMED_BUT_LIMITED")
    _seed_limitation(tmp_path)
    _seed_acceptance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_RECONCILIATION_PRECONDITION_FAILED"
    assert report["criteria"]["significance_outcome_matches_required"] is False


def test_scope_violation_when_any_input_scope_mismatches(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path, comparator_id="OV-RL-10-ALT")
    _seed_limitation(tmp_path)
    _seed_acceptance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_RECONCILIATION_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_reconciliation_preserves_non_promotion_non_closure_guards(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path)
    _seed_acceptance(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    assert "PROMOTION" not in report["summary"]["next_action"]
    assert "CLOSURE" not in report["summary"]["next_action"]
