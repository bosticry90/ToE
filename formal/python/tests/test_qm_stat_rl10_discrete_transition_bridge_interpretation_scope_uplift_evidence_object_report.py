from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_evidence_object_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_post_acceptance_uplift_surface_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_post_acceptance_uplift_surface_20260422_v0.json",
                "bridge_interpretation_scope_reconciliation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_interpretation_scope_reconciliation_review_20260422_v0.json",
                "bridge_limitation_mapping_normalization_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_20260422_v0.json",
                "bridge_signal_margin_limitation_acceptance_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v1.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "evidence_object_policy": {
                "required_uplift_surface_outcome": "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_READY_FOR_BOUNDED_EVIDENCE_OBJECT",
                "required_admissible_evidence_class": "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
                "required_admissible_evidence_object_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
                "required_reconciliation_outcome": "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED",
                "required_normalization_outcome": "LIMITATION_MAPPING_NORMALIZATION_COMPLETED",
                "required_acceptance_outcome": "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING",
                "evidence_object_question": "What bounded evidence could replace LIMITATION_INTERPRETATION_SCOPE_HOLD with a declared post-acceptance uplift state?",
                "uplift_gate_id": "rl10_interpretation_scope_uplift_evidence_gate_v0",
                "uplift_gate_contract": "SINGLE_BOUNDED_GATE_EXECUTION_ONLY",
                "falsification_condition": "EVIDENCE_OBJECT_GATE_FAILS_OR_NO_SCOPE_CHANGE_FROM_ACCEPTED_CURRENT_CEILING",
                "stop_condition_if_not_met": "REMAIN_FROZEN_AND_DO_NOT_REOPEN_BRANCH_EXECUTION",
                "single_bounded_execution_object_only": True,
                "no_expansion_no_rollout_guard": True,
                "implicitly_authorizes_promotion": False,
                "implicitly_authorizes_multi_lane_expansion": False,
                "implicitly_authorizes_rollout": False,
                "non_promotion_non_closure_boundary": True,
                "branch_execution_reopened": False,
            },
            "evidence_object_contract": {
                "allowed_outcomes": [
                    "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARED_AND_GATE_READY",
                    "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARATION_INVALID",
                    "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_OUTCOME",
                "no_loop_rule": "DECLARATION_ONLY_NO_EXECUTION_REOPEN_IN_THIS_PACKET",
                "default_outcome": "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARATION_INVALID",
            },
        },
    )


def _seed_uplift_surface_report(
    root: Path,
    *,
    outcome: str = "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_READY_FOR_BOUNDED_EVIDENCE_OBJECT",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
    admissible_class: str = "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
    admissible_object_id: str = "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_post_acceptance_uplift_surface_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {
                "inputs": {
                    "admissible_evidence_class": admissible_class,
                    "admissible_evidence_object_id": admissible_object_id,
                }
            },
        },
    )


def _seed_reconciliation_report(
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


def _seed_normalization_report(
    root: Path,
    *,
    outcome: str = "LIMITATION_MAPPING_NORMALIZATION_COMPLETED",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )


def _seed_acceptance_report(
    root: Path,
    *,
    outcome: str = "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v1.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )


def test_declared_and_gate_ready_when_all_preconditions_and_guards_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_uplift_surface_report(tmp_path)
    _seed_reconciliation_report(tmp_path)
    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARED_AND_GATE_READY"
    assert report["summary"]["branch_execution_reopened"] is False


def test_declaration_invalid_when_branch_execution_reopened_true(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["evidence_object_policy"]["branch_execution_reopened"] = True
    _write_json(declaration_path, payload)

    _seed_uplift_surface_report(tmp_path)
    _seed_reconciliation_report(tmp_path)
    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARATION_INVALID"
    assert report["criteria"]["branch_execution_reopened_is_false"] is False


def test_declaration_invalid_when_admissible_object_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_uplift_surface_report(
        tmp_path,
        admissible_object_id="SOME_OTHER_OBJECT_v0",
    )
    _seed_reconciliation_report(tmp_path)
    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARATION_INVALID"
    assert report["criteria"]["admissible_evidence_object_id_matches"] is False


def test_scope_violation_when_any_input_scope_mismatches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_uplift_surface_report(tmp_path, comparator_id="OV-RL-10-ALT")
    _seed_reconciliation_report(tmp_path)
    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_declaration_invalid_when_falsification_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["evidence_object_policy"]["falsification_condition"] = ""
    _write_json(declaration_path, payload)

    _seed_uplift_surface_report(tmp_path)
    _seed_reconciliation_report(tmp_path)
    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_DECLARATION_INVALID"
    assert report["criteria"]["declared_text_fields_present"] is False
