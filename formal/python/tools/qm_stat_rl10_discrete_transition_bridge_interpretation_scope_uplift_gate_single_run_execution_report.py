from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTION_20260422_v0.json"
)

_REQUIRED_TEXT_FIELDS = (
    "falsification_condition",
    "stop_condition_if_not_met",
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _norm(value: Any) -> str:
    return str(value or "").strip()


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    seam_scope = dict(declaration.get("seam_scope", {}))
    policy = dict(declaration.get("single_run_policy", {}))
    contract = dict(declaration.get("single_run_contract", {}))

    execution_packet_path = REPO_ROOT / _norm(
        required_inputs.get("bridge_interpretation_scope_uplift_gate_execution_packet_report")
    )
    execution_packet = _read_json(execution_packet_path)

    packet_summary = dict(execution_packet.get("summary", {}))
    packet_inputs = dict(dict(execution_packet.get("objective_quality", {})).get("inputs", {}))

    expected_comparator_id = _norm(seam_scope.get("external_comparator_id"))
    expected_quantity_id = _norm(seam_scope.get("bridge_quantity_id"))

    required_packet_outcome = _norm(policy.get("required_execution_packet_outcome"))
    required_packet_id = _norm(policy.get("required_execution_packet_id"))
    required_execution_mode = _norm(policy.get("required_execution_mode"))
    required_evidence_class = _norm(policy.get("required_admissible_evidence_class"))
    required_evidence_object_id = _norm(policy.get("required_admissible_evidence_object_id"))
    required_uplift_gate_id = _norm(policy.get("required_uplift_gate_id"))
    required_uplift_gate_contract = _norm(policy.get("required_uplift_gate_contract"))

    packet_outcome = _norm(packet_summary.get("review_outcome"))
    packet_id = _norm(packet_summary.get("execution_packet_id"))
    execution_mode = _norm(packet_summary.get("execution_mode"))
    evidence_class = _norm(packet_summary.get("admissible_evidence_class"))
    evidence_object_id = _norm(packet_summary.get("admissible_evidence_object_id"))
    uplift_gate_id = _norm(packet_inputs.get("required_uplift_gate_id", packet_inputs.get("observed_uplift_gate_id")))
    uplift_gate_contract = _norm(
        packet_inputs.get("required_uplift_gate_contract", packet_inputs.get("observed_uplift_gate_contract"))
    )

    packet_comparator_id = _norm(packet_summary.get("external_comparator_id"))
    packet_quantity_id = _norm(packet_summary.get("bridge_quantity_id"))
    scope_match = packet_comparator_id == expected_comparator_id and packet_quantity_id == expected_quantity_id

    packet_outcome_matches = packet_outcome == required_packet_outcome
    packet_id_matches = packet_id == required_packet_id
    execution_mode_matches = execution_mode == required_execution_mode
    evidence_class_matches = evidence_class == required_evidence_class
    evidence_object_id_matches = evidence_object_id == required_evidence_object_id
    uplift_gate_id_matches = uplift_gate_id == required_uplift_gate_id
    uplift_gate_contract_matches = uplift_gate_contract == required_uplift_gate_contract

    single_run_executed = bool(policy.get("single_run_executed", False))
    scope_change_signal_observed = bool(policy.get("scope_change_signal_observed", False))
    branch_execution_reopened_by_run = bool(policy.get("branch_execution_reopened_by_run", False))

    single_bounded_run_only = bool(policy.get("single_bounded_run_only", False))
    no_expansion_no_rollout_guard = bool(policy.get("no_expansion_no_rollout_guard", False))
    non_promotion_non_closure_boundary = bool(policy.get("non_promotion_non_closure_boundary", False))

    implicitly_authorizes_promotion = bool(policy.get("implicitly_authorizes_promotion", False))
    implicitly_authorizes_multi_lane_expansion = bool(policy.get("implicitly_authorizes_multi_lane_expansion", False))
    implicitly_authorizes_rollout = bool(policy.get("implicitly_authorizes_rollout", False))
    promotion_expansion_rollout_disallowed = (
        not implicitly_authorizes_promotion
        and not implicitly_authorizes_multi_lane_expansion
        and not implicitly_authorizes_rollout
    )

    declared_text_fields_present = all(_norm(policy.get(field)) for field in _REQUIRED_TEXT_FIELDS)

    preconditions_satisfied = (
        packet_outcome_matches
        and packet_id_matches
        and execution_mode_matches
        and evidence_class_matches
        and evidence_object_id_matches
        and uplift_gate_id_matches
        and uplift_gate_contract_matches
        and single_bounded_run_only
        and no_expansion_no_rollout_guard
        and non_promotion_non_closure_boundary
        and promotion_expansion_rollout_disallowed
        and declared_text_fields_present
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        run_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_SCOPE_VIOLATION"
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied or not single_run_executed:
        run_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_PRECONDITION_FAILED"
        next_action = "REPAIR_SINGLE_RUN_PRECONDITIONS_BEFORE_EXECUTION"
    elif scope_change_signal_observed:
        run_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTED_SCOPE_CHANGE_SIGNAL_OBSERVED"
        next_action = "AUTHOR_DECLARED_POST_RUN_SCOPE_CHANGE_REVIEW_PACKET_ONCE"
    else:
        run_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_EXECUTED_NO_SCOPE_CHANGE_REMAIN_FROZEN"
        next_action = "REMAIN_FROZEN_AND_STOP_PENDING_NEW_DECLARED_UPLIFT_SURFACE"

    if run_outcome not in allowed_outcomes:
        run_outcome = _norm(
            contract.get(
                "default_outcome",
                "INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_PRECONDITION_FAILED",
            )
        )

    branch_execution_reopened = branch_execution_reopened_by_run

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_packet_outcome_matches_required": packet_outcome_matches,
            "execution_packet_id_matches_required": packet_id_matches,
            "execution_mode_matches_required": execution_mode_matches,
            "admissible_evidence_class_matches": evidence_class_matches,
            "admissible_evidence_object_id_matches": evidence_object_id_matches,
            "uplift_gate_id_matches": uplift_gate_id_matches,
            "uplift_gate_contract_matches": uplift_gate_contract_matches,
            "single_run_executed": single_run_executed,
            "declared_text_fields_present": declared_text_fields_present,
            "single_bounded_run_only": single_bounded_run_only,
            "no_expansion_no_rollout_guard": no_expansion_no_rollout_guard,
            "non_promotion_non_closure_boundary": non_promotion_non_closure_boundary,
            "promotion_expansion_rollout_disallowed": promotion_expansion_rollout_disallowed,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": _norm(contract.get("no_loop_rule"))
            == "ONE_DECLARED_SINGLE_RUN_EXECUTION_ONLY",
            "single_terminal_outcome_rule_declared": _norm(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_UPLIFT_GATE_SINGLE_RUN_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": run_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "single_run_execution_answered": True,
            },
            "inputs": {
                "required_execution_packet_outcome": required_packet_outcome,
                "observed_execution_packet_outcome": packet_outcome,
                "required_execution_packet_id": required_packet_id,
                "observed_execution_packet_id": packet_id,
                "required_execution_mode": required_execution_mode,
                "observed_execution_mode": execution_mode,
                "required_uplift_gate_id": required_uplift_gate_id,
                "observed_uplift_gate_id": uplift_gate_id,
                "required_uplift_gate_contract": required_uplift_gate_contract,
                "observed_uplift_gate_contract": uplift_gate_contract,
                "scope_change_signal_observed": scope_change_signal_observed,
                "branch_execution_reopened_by_run": branch_execution_reopened_by_run,
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (run_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "run_outcome": run_outcome,
            "single_run_executed": single_run_executed,
            "scope_change_signal_observed": scope_change_signal_observed,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "execution_packet_id": required_packet_id,
            "execution_mode": required_execution_mode,
            "branch_execution_reopened": branch_execution_reopened,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_interpretation_scope_uplift_gate_execution_packet_report": _ptr(execution_packet_path),
        },
        "non_claim_boundary": "Repository-local interpretation-scope uplift gate single-run execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge interpretation-scope uplift gate single-run execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_single_run_execution_20260422_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_single_run_execution_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
