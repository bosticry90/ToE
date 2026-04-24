from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_execution_packet_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_interpretation_scope_uplift_gate_artifact_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_artifact_20260422_v0.json"
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "uplift_gate_execution_packet_policy": {
                "required_gate_artifact_outcome": "INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_DECLARED_AND_SINGLE_RUN_READY",
                "required_gate_artifact_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_v0",
                "required_admissible_evidence_class": "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
                "required_admissible_evidence_object_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
                "required_uplift_gate_id": "rl10_interpretation_scope_uplift_evidence_gate_v0",
                "required_uplift_gate_contract": "SINGLE_BOUNDED_GATE_EXECUTION_ONLY",
                "execution_packet_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_v0",
                "execution_packet_question": "What exact single bounded uplift-gate run should execute now without reopening branch execution?",
                "execution_mode": "SINGLE_BOUNDED_UPLIFT_GATE_RUN_ONCE",
                "execution_success_condition": "DECLARED_SINGLE_RUN_RETURNS_DECLARED_POST_ACCEPTANCE_UPLIFT_STATE_CHANGE_SIGNAL",
                "falsification_condition": "UPLIFT_GATE_RUN_FAILS_OR_REPRODUCES_ACCEPTED_CURRENT_CEILING_WITH_NO_SCOPE_CHANGE",
                "stop_condition_if_not_met": "REMAIN_FROZEN_AND_DO_NOT_REOPEN_BRANCH_EXECUTION",
                "single_bounded_run_only": True,
                "no_expansion_no_rollout_guard": True,
                "implicitly_authorizes_promotion": False,
                "implicitly_authorizes_multi_lane_expansion": False,
                "implicitly_authorizes_rollout": False,
                "non_promotion_non_closure_boundary": True,
                "branch_execution_reopened": False,
            },
            "uplift_gate_execution_packet_contract": {
                "allowed_outcomes": [
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARED_AND_SINGLE_RUN_AUTHORIZED",
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARATION_INVALID",
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_OUTCOME",
                "no_loop_rule": "DECLARATION_ONLY_NO_EXECUTION_REOPEN_IN_THIS_PACKET",
                "default_outcome": "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARATION_INVALID",
            },
        },
    )


def _seed_artifact_report(
    root: Path,
    *,
    outcome: str = "INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_DECLARED_AND_SINGLE_RUN_READY",
    artifact_id: str = "RL10_INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_v0",
    admissible_class: str = "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
    admissible_object_id: str = "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
    gate_id: str = "rl10_interpretation_scope_uplift_evidence_gate_v0",
    gate_contract: str = "SINGLE_BOUNDED_GATE_EXECUTION_ONLY",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
    branch_execution_reopened: bool = False,
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_artifact_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "uplift_gate_artifact_id": artifact_id,
                "admissible_evidence_class": admissible_class,
                "admissible_evidence_object_id": admissible_object_id,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "branch_execution_reopened": branch_execution_reopened,
            },
            "objective_quality": {
                "inputs": {
                    "observed_uplift_gate_id": gate_id,
                    "observed_uplift_gate_contract": gate_contract,
                }
            },
        },
    )


def test_declared_and_single_run_authorized_when_all_preconditions_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_artifact_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["review_outcome"]
        == "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARED_AND_SINGLE_RUN_AUTHORIZED"
    )
    assert report["summary"]["branch_execution_reopened"] is False


def test_declaration_invalid_when_branch_execution_reopened_true(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["uplift_gate_execution_packet_policy"]["branch_execution_reopened"] = True
    _write_json(declaration_path, payload)
    _seed_artifact_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARATION_INVALID"
    assert report["criteria"]["branch_execution_reopened_is_false"] is False


def test_declaration_invalid_when_required_gate_id_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_artifact_report(tmp_path, gate_id="wrong_gate")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARATION_INVALID"
    assert report["criteria"]["uplift_gate_id_matches"] is False


def test_scope_violation_when_input_scope_mismatches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_artifact_report(tmp_path, comparator_id="OV-RL-10-ALT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_declaration_invalid_when_required_text_field_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["uplift_gate_execution_packet_policy"]["falsification_condition"] = ""
    _write_json(declaration_path, payload)
    _seed_artifact_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARATION_INVALID"
    assert report["criteria"]["declared_text_fields_present"] is False
