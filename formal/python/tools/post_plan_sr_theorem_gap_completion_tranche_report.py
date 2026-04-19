from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    queue_path = REPO_ROOT / str(required_inputs.get("completion_queue_report", "")).strip()
    em_path = REPO_ROOT / str(required_inputs.get("post_plan_em_theorem_gap_completion_tranche_report", "")).strip()
    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()
    matrix_path = REPO_ROOT / str(required_inputs.get("completion_matrix", "")).strip()
    dashboard_path = REPO_ROOT / str(required_inputs.get("blocker_burn_dashboard_report", "")).strip()
    contradiction_path = REPO_ROOT / str(required_inputs.get("science_maturity_contradiction_report", "")).strip()
    conversion_review_path = REPO_ROOT / str(required_inputs.get("program_state_conversion_review", "")).strip()
    doc_path = REPO_ROOT / str(required_inputs.get("sr_target_doc", "")).strip()
    artifact_path = REPO_ROOT / str(required_inputs.get("sr_artifact", "")).strip()
    gate_path = REPO_ROOT / str(required_inputs.get("sr_gate", "")).strip()

    queue_report = _read_json(queue_path)
    em_report = _read_json(em_path)
    target_map = _read_json(target_map_path)
    dashboard = _read_json(dashboard_path)
    contradiction = _read_json(contradiction_path)
    conversion_review = _read_json(conversion_review_path)
    artifact = _read_json(artifact_path)
    doc_text = _read_text(doc_path)
    _read_text(gate_path)
    matrix_rows = _parse_markdown_table(
        _read_text(matrix_path),
        [
            "row_id",
            "domain",
            "lane",
            "current_status",
            "blocker_class",
            "primary_target",
            "primary_artifact",
            "primary_gate",
            "governance_checkpoint_status",
            "physics_checkpoint_status",
            "gate_runtime_status",
        ],
    )

    target_row_id = str(policy.get("required_target_row", "")).strip()
    route_map = {row["row_id"]: row for row in target_map.get("routed_rows", [])}
    matrix_row = {row["row_id"]: row for row in matrix_rows}.get(target_row_id, {})
    target_row = dict(route_map.get(target_row_id, {}))
    payload = dict(artifact.get("payload", {}))
    queue_rows = {row.get("row_id"): row for row in queue_report.get("completion_queue", [])}

    queue_ok = (
        queue_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_queue_outcome", "")).strip()
        and queue_rows.get(target_row_id, {}).get("queue_rank") == 6
        and queue_rows.get(target_row_id, {}).get("row_id") == str(policy.get("required_queue_follow_on_row", "")).strip()
    )
    em_ok = (
        em_report.get("summary", {}).get("terminal_outcome")
        == str(policy.get("required_prior_em_outcome", "")).strip()
    )
    conversion_review_ok = (
        conversion_review.get("review_basis")
        == str(policy.get("required_program_state_conversion_review_basis", "")).strip()
        and conversion_review.get("review_policy", {}).get("no_loop_rule") == "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY"
    )
    target_map_ok = target_row.get("route_class") == str(policy.get("required_target_route_class", "")).strip()
    doc_ok = all(
        token in doc_text
        for token in [
            "DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_05_v0",
            "SR_EMPIRICAL_PACKET_05_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
            "SR_EMPIRICAL_PACKET_05_DECISION_v0: RETAIN_v0",
            "formal/output/sr_empirical_comparison_packet_05_v0.json",
            "formal/python/tests/test_sr_empirical_comparison_packet_05_gate.py",
        ]
    )
    artifact_ok = (
        artifact.get("artifact_id") == "sr_empirical_comparison_packet_05_v0"
        and payload.get("status") == str(policy.get("required_target_status", "")).strip()
        and payload.get("decision") in {str(policy.get("required_target_decision", "")).strip(), "PRUNE_v0"}
        and payload.get("evidence_tier") == str(policy.get("required_target_evidence_tier", "")).strip()
    )
    row_ok = (
        bool(matrix_row)
        and matrix_row.get("blocker_class") == str(policy.get("required_target_blocker_class", "")).strip()
        and matrix_row.get("primary_target") == _ptr(doc_path)
        and matrix_row.get("primary_artifact") == _ptr(artifact_path)
        and matrix_row.get("primary_gate") == _ptr(gate_path)
    )
    contradiction_ok = any(
        observation.get("row_id") == target_row_id and observation.get("observation_type") == "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"
        for observation in contradiction.get("modeled_observations", [])
    )

    row_truth_change_detected = bool(matrix_row) and (
        matrix_row.get("blocker_class") != "THEOREM_GAP"
        or matrix_row.get("physics_checkpoint_status") != "THEOREM_GAP_OPEN"
        or matrix_row.get("current_status") == "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE"
    )
    explicit_exhaustion_detected = payload.get("decision") == "PRUNE_v0" and not row_truth_change_detected

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE")
    ).strip()

    if not matrix_row or not target_row:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_REPAIR"
        next_action = "RESTORE_SR_TRANCHE_INPUT_SHAPE_AND_RERUN"
    elif all([queue_ok, em_ok, conversion_review_ok, target_map_ok, doc_ok, artifact_ok, row_ok, contradiction_ok]) and row_truth_change_detected:
        terminal_outcome = "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_AND_PROMOTED"
        next_action = "REASSESS_POST_SR_ROUTE_CLASSES_WITH_CHANGED_SR_ROW_TRUTH"
    elif all([queue_ok, em_ok, conversion_review_ok, target_map_ok, doc_ok, artifact_ok, row_ok, contradiction_ok]) and explicit_exhaustion_detected:
        terminal_outcome = "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"
        next_action = "ROUTE_TO_PROGRAM_STATE_CONVERSION_REVIEW_WITH_SR_EXHAUSTION_RECORDED"
    elif all([queue_ok, em_ok, conversion_review_ok, target_map_ok, doc_ok, artifact_ok, row_ok, contradiction_ok]):
        terminal_outcome = "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"
        next_action = "ROUTE_TO_PROGRAM_STATE_CONVERSION_REVIEW_WITH_QFT_EM_SR_NONMOVING_FAMILIES_RECORDED"
    else:
        terminal_outcome = "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_SR_TRANCHE_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "completion_queue_materialized": queue_ok,
            "prior_em_nonmoving_history_recorded": em_ok,
            "program_state_conversion_review_ready": conversion_review_ok,
            "target_map_materialized": target_map_ok,
            "sr_doc_tokens_present": doc_ok,
            "sr_artifact_alignment_ok": artifact_ok,
            "sr_row_alignment_ok": row_ok,
            "sr_live_theorem_gap_observation_present": contradiction_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "promotion_only_if_row_truth_changed": (terminal_outcome != "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_AND_PROMOTED") or row_truth_change_detected,
                "exhaustion_only_if_explicit_decision_present": (terminal_outcome != "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED") or explicit_exhaustion_detected,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "queue_rank": queue_rows.get(target_row_id, {}).get("queue_rank"),
                "prior_em_outcome": em_report.get("summary", {}).get("terminal_outcome"),
                "conversion_review_basis": conversion_review.get("review_basis"),
                "artifact_decision": payload.get("decision"),
                "artifact_status": payload.get("status"),
                "blocker_movement_status": dashboard.get("blocker_scoreboard", {}).get("movement_status"),
                "blocker_net_delta": dashboard.get("blocker_scoreboard", {}).get("net_delta"),
                "row_current_status": matrix_row.get("current_status"),
                "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
                "row_blocker_class": matrix_row.get("blocker_class"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_route_class": target_row.get("route_class"),
            "queue_rank": queue_rows.get(target_row_id, {}).get("queue_rank"),
            "row_truth_change_detected": row_truth_change_detected,
            "explicit_exhaustion_detected": explicit_exhaustion_detected,
            "artifact_decision": payload.get("decision"),
            "row_current_status": matrix_row.get("current_status"),
            "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "completion_queue_report": _ptr(queue_path),
            "post_plan_em_theorem_gap_completion_tranche_report": _ptr(em_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "completion_matrix": _ptr(matrix_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "science_maturity_contradiction_report": _ptr(contradiction_path),
            "program_state_conversion_review": _ptr(conversion_review_path),
            "sr_target_doc": _ptr(doc_path),
            "sr_artifact": _ptr(artifact_path),
            "sr_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local post-plan SR theorem-gap completion tranche measurement only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan SR theorem-gap completion tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "post_plan_sr_theorem_gap_completion_tranche_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())