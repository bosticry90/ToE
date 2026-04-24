from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_report as tool,
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
                "bridge_interpretation_scope_reconciliation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_interpretation_scope_reconciliation_review_20260422_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "normalization_policy": {
                "required_reconciliation_outcome": "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED",
                "required_significance_outcome": "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE",
                "required_limitation_outcome": "LIMITATION_INTERPRETATION_SCOPE_HOLD",
                "required_limitation_primary_cause": "interpretation_scope_or_path_validity_not_sufficient_for_advancement",
                "not_a_new_hardening_cycle": True,
                "no_scope_expansion": True,
            },
            "normalization_contract": {
                "allowed_outcomes": [
                    "LIMITATION_MAPPING_NORMALIZATION_COMPLETED",
                    "LIMITATION_MAPPING_NORMALIZATION_NOT_REQUIRED",
                    "LIMITATION_MAPPING_NORMALIZATION_PRECONDITION_FAILED",
                    "LIMITATION_MAPPING_NORMALIZATION_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_LIMITATION_MAPPING_NORMALIZATION_OUTCOME",
                "no_loop_rule": "ONE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_ONLY",
                "default_outcome": "LIMITATION_MAPPING_NORMALIZATION_PRECONDITION_FAILED",
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
            }
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
            }
        },
    )


def _seed_reconciliation(
    root: Path,
    *,
    outcome: str = "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_reconciliation_review_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )


def test_normalization_completed_when_reconciliation_confirms_mapping_mismatch(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path)
    _seed_reconciliation(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "LIMITATION_MAPPING_NORMALIZATION_COMPLETED"
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True


def test_precondition_failed_when_reconciliation_outcome_not_mapping_mismatch(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path)
    _seed_reconciliation(tmp_path, outcome="INTERPRETATION_SCOPE_SHIFT_CONFIRMED_AS_CORRECT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "LIMITATION_MAPPING_NORMALIZATION_PRECONDITION_FAILED"
    assert report["criteria"]["reconciliation_outcome_matches_required"] is False


def test_precondition_failed_when_limitation_outcome_not_scope_hold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path, outcome="LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD")
    _seed_reconciliation(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "LIMITATION_MAPPING_NORMALIZATION_PRECONDITION_FAILED"
    assert report["criteria"]["limitation_outcome_matches_required"] is False


def test_scope_violation_when_scope_mismatches(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path, comparator_id="OV-RL-10-ALT")
    _seed_limitation(tmp_path)
    _seed_reconciliation(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "LIMITATION_MAPPING_NORMALIZATION_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_normalization_enforces_non_expansion_boundary_guards(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance(tmp_path)
    _seed_limitation(tmp_path)
    _seed_reconciliation(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["criteria"]["scope_guards_satisfied"] is True
    assert "PROMOTION" not in report["summary"]["next_action"]
    assert "CLOSURE" not in report["summary"]["next_action"]
