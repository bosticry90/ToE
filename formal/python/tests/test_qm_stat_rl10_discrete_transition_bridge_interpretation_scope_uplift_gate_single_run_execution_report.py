from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_single_run_execution_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_interpretation_scope_uplift_gate_execution_packet_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_execution_packet_20260422_v0.json"
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "single_run_policy": {
                "required_execution_packet_outcome": "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARED_AND_SINGLE_RUN_AUTHORIZED",
                "required_execution_packet_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_v0",
                "required_execution_mode": "SINGLE_BOUNDED_UPLIFT_GATE_RUN_ONCE",
                "required_admissible_evidence_class": "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
                "required_admissible_evidence_object_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
                "required_uplift_gate_id": "rl10_interpretation_scope_uplift_evidence_gate_v0",
                "required_uplift_gate_contract": "SINGLE_BOUNDED_GATE_EXECUTION_ONLY",
                "single_run_executed": True,
                "scope_change_signal_observed": False,
                "branch_execution_reopened_by_run": False,
                "single_bounded_run_only": True,
                "no_expansion_no_rollout_guard": True,
                "implicitly_authorizes_promotion": False,
                "implicitly_authorizes_multi_lane_expansion": False,
                "implicitly_authorizes_rollout": False,
                "non_promotion_non_closure_boundary": True,
                "falsification_condition": "SINGLE_RUN_FAILS_OR_RETURNS_NO_DECLARED_SCOPE_CHANGE_SIGNAL",
                "stop_condition_if_not_met": "REMAIN_FROZEN_AND_DO_NOT_REOPEN_BRANCH_EXECUTION",
            },
            "single_run_contract": {
                "allowed_outcomes": [
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTED_NO_SCOPE_CHANGE_REMAIN_FROZEN",
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTED_SCOPE_CHANGE_SIGNAL_OBSERVED",
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_PRECONDITION_FAILED",
                    "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_OUTCOME",
                "no_loop_rule": "ONE_DECLARED_SINGLE_RUN_EXECUTION_ONLY",
                "default_outcome": "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_PRECONDITION_FAILED",
            },
        },
    )


def _seed_execution_packet_report(
    root: Path,
    *,
    outcome: str = "INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARED_AND_SINGLE_RUN_AUTHORIZED",
    packet_id: str = "RL10_INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_v0",
    execution_mode: str = "SINGLE_BOUNDED_UPLIFT_GATE_RUN_ONCE",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
    gate_id: str = "rl10_interpretation_scope_uplift_evidence_gate_v0",
    gate_contract: str = "SINGLE_BOUNDED_GATE_EXECUTION_ONLY",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_execution_packet_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "execution_packet_id": packet_id,
                "execution_mode": execution_mode,
                "admissible_evidence_class": "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
                "admissible_evidence_object_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {
                "inputs": {
                    "required_uplift_gate_id": gate_id,
                    "required_uplift_gate_contract": gate_contract,
                }
            },
        },
    )


def test_single_run_executes_no_scope_change_and_remains_frozen(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_execution_packet_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["run_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTED_NO_SCOPE_CHANGE_REMAIN_FROZEN"
    assert report["summary"]["branch_execution_reopened"] is False


def test_single_run_scope_change_signal_observed_path(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["single_run_policy"]["scope_change_signal_observed"] = True
    _write_json(declaration_path, payload)
    _seed_execution_packet_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["run_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTED_SCOPE_CHANGE_SIGNAL_OBSERVED"


def test_precondition_failed_on_wrong_execution_packet_outcome(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_execution_packet_report(
        tmp_path,
        outcome="INTERPRETATION_SCOPE_UPLIFT_GATE_EXECUTION_PACKET_DECLARATION_INVALID",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["run_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_PRECONDITION_FAILED"
    assert report["criteria"]["execution_packet_outcome_matches_required"] is False


def test_scope_violation_when_scope_mismatches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_execution_packet_report(tmp_path, comparator_id="OV-RL-10-ALT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["run_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_precondition_failed_when_single_run_not_executed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["single_run_policy"]["single_run_executed"] = False
    _write_json(declaration_path, payload)
    _seed_execution_packet_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["run_outcome"] == "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_PRECONDITION_FAILED"
    assert report["criteria"]["single_run_executed"] is False
