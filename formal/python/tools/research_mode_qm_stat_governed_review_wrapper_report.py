from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_GOVERNED_REVIEW_WRAPPER_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_GOVERNED_REVIEW_WRAPPER_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_governed_review_wrapper_20260419_v0.json"
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


def _latest_active_definition(entries: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    active_entries = [
        entry
        for entry in entries
        if entry.get("target_row_id") == row_id and entry.get("status") == "ACTIVE"
    ]
    return dict(active_entries[-1]) if active_entries else {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    execution_policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    payload_path = REPO_ROOT / str(required_inputs.get("payload_record", "")).strip()
    comparison_path = REPO_ROOT / str(required_inputs.get("comparison_report", "")).strip()
    witness_binding_path = REPO_ROOT / str(required_inputs.get("witness_binding", "")).strip()
    blocker_definitions_path = REPO_ROOT / str(required_inputs.get("blocker_definitions", "")).strip()
    payload_requirements_path = REPO_ROOT / str(required_inputs.get("payload_requirements", "")).strip()
    promotion_policy_path = REPO_ROOT / str(required_inputs.get("promotion_lane_policy", "")).strip()
    mutation_protocol_path = REPO_ROOT / str(required_inputs.get("canonical_mutation_protocol", "")).strip()

    payload = _read_json(payload_path)
    comparison = _read_json(comparison_path)
    witness_binding = _read_json(witness_binding_path)
    blocker_definitions = _read_json(blocker_definitions_path)
    payload_requirements_text = _read_text(payload_requirements_path)
    promotion_policy_text = _read_text(promotion_policy_path)
    mutation_protocol_text = _read_text(mutation_protocol_path)

    payload_metadata = dict(payload.get("metadata_record", {}))
    payload_binding = dict(payload.get("target_binding", {}))
    comparison_summary = dict(comparison.get("summary", {}))
    comparison_objective = dict(comparison.get("objective_quality", {}))
    comparison_criteria = dict(comparison_objective.get("criteria", {}))
    comparison_record = dict(comparison.get("comparison_record", {}))
    payload_candidate = dict(comparison_record.get("payload_candidate", {}))
    harder_target = dict(comparison_record.get("harder_target", {}))
    active_definition = _latest_active_definition(list(blocker_definitions.get("entries", [])), str(payload_binding.get("row_id", "")))

    payload_contract_ok = all(
        token in payload_requirements_text
        for token in (
            "SANDBOX_PROMOTION_PAYLOAD_DECISION_SET_v0: PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
            "SANDBOX_PROMOTION_PAYLOAD_FAIL_CLOSED_RULE_v0: MISSING_METADATA_OR_TARGET_BINDING_OR_CONTRADICTION_CHECK_OR_MUTATION_PLAN_IS_HARD_FAIL",
        )
    )
    promotion_policy_ok = all(
        token in promotion_policy_text
        for token in (
            "PROMOTION_GOVERNANCE_LANE_PROMOTION_RULE_v0: CANONICAL_ROW_AND_SEAM_STATE_CHANGE_ONLY_AFTER_GOVERNED_PROMOTION_PASS",
            "PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW",
        )
    )
    mutation_protocol_ok = all(
        token in mutation_protocol_text
        for token in (
            "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_EMISSION_RULE_v0: EMIT_ONLY_ON_GOVERNED_PROMOTION_REVIEW_PROMOTE_DECISION",
            "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_NOOP_RULE_v0: HOLD_OR_REJECT_DECISION_EMITS_NO_CANONICAL_MUTATION",
        )
    )
    payload_primary_object_ok = payload.get("artifact_pointer") == comparison_objective.get("inputs", {}).get(
        "payload_artifact_pointer"
    ) and payload.get("contract_bindings", {}).get("comparison_surface") == _ptr(comparison_path)
    target_binding_ok = (
        payload_binding.get("row_id") == str(execution_policy.get("required_target_row", "")).strip()
        and payload_binding.get("seam_id") == str(execution_policy.get("required_target_seam", "")).strip()
        and payload_binding.get("target_package_id") == str(execution_policy.get("required_target_package_id", "")).strip()
        and payload_binding.get("row_id") == witness_binding.get("row_id")
        and payload_binding.get("target_package_id") == witness_binding.get("target_package_id")
    )
    payload_ready = (
        payload.get("decision_boundary") == str(execution_policy.get("required_payload_decision_boundary", "")).strip()
        and payload_metadata.get("artifact_class") == str(execution_policy.get("required_payload_artifact_class", "")).strip()
        and payload_metadata.get("promotion_readiness") == str(execution_policy.get("required_promotion_readiness", "")).strip()
        and payload_metadata.get("delta_class") == str(execution_policy.get("required_primary_delta_class", "")).strip()
        and payload.get("summary", {}).get("payload_status_v0") == "READY_FOR_COMPARISON_BUNDLE_v0_NONCLAIM"
        and str(payload.get("contradiction_check_result", "")).startswith("PASS_")
    )
    comparison_aligned = (
        comparison_summary.get("comparison_status_v0") == "ALIGNED_BOUNDED_v0_NONCLAIM"
        and comparison_summary.get("row_id") == payload_binding.get("row_id")
        and comparison_summary.get("seam_id") == payload_binding.get("seam_id")
        and comparison_summary.get("target_package_id") == payload_binding.get("target_package_id")
        and comparison_criteria.get("all_criteria_pass") is True
        and comparison_record.get("comparison_disposition_v0")
        == "PAYLOAD_REMAINS_PRIMARY_GOVERNED_ENTRY_OBJECT_HARDER_TARGET_REMAINS_BOUND_SUPPORTING_EVIDENCE"
        and harder_target.get("promotability") == "NOT_READY"
    )
    authority_support_ready = (
        active_definition.get("definition_id") == str(execution_policy.get("required_blocker_definition_id", "")).strip()
        and active_definition.get("coupling_state") == str(execution_policy.get("required_coupling_state", "")).strip()
        and active_definition.get("promotion_ruling") == str(execution_policy.get("required_promotion_ruling", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "QM_STAT_GOVERNED_REVIEW_WRAPPER_NOT_READY")).strip()

    if not all([payload_contract_ok, promotion_policy_ok, mutation_protocol_ok, payload_primary_object_ok, target_binding_ok, payload_ready]):
        terminal_outcome = "QM_STAT_GOVERNED_REVIEW_WRAPPER_NOT_READY"
        governed_decision = "not_ready"
        next_action = str(execution_policy.get("required_wrapper_next_action_on_not_ready", "")).strip()
    elif not comparison_aligned:
        terminal_outcome = "QM_STAT_GOVERNED_REVIEW_WRAPPER_BLOCKED_BY_COMPARISON_MISMATCH"
        governed_decision = "blocked_by_comparison_mismatch"
        next_action = str(execution_policy.get("required_wrapper_next_action_on_comparison_block", "")).strip()
    elif not authority_support_ready:
        terminal_outcome = "QM_STAT_GOVERNED_REVIEW_WRAPPER_REQUIRES_ADDITIONAL_SUPPORT"
        governed_decision = "requires_additional_support"
        next_action = str(execution_policy.get("required_wrapper_next_action_on_additional_support", "")).strip()
    else:
        terminal_outcome = "QM_STAT_GOVERNED_REVIEW_WRAPPER_READY_FOR_BOUNDED_SANDBOX_REVIEW"
        governed_decision = "ready_for_bounded_sandbox_review"
        next_action = str(execution_policy.get("required_wrapper_next_action_on_ready", "")).strip()

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "payload_requirement_tokens_present": payload_contract_ok,
            "promotion_policy_tokens_present": promotion_policy_ok,
            "mutation_protocol_tokens_present": mutation_protocol_ok,
            "payload_is_primary_object": payload_primary_object_ok,
            "target_binding_matches_live_anchor": target_binding_ok,
            "payload_ready_for_intake": payload_ready,
            "comparison_surface_aligned": comparison_aligned,
            "authority_support_ready": authority_support_ready,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_GOVERNED_REVIEW_WRAPPER_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_GOVERNED_REVIEW_WRAPPER_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "primary_payload_preserved": payload_candidate.get("artifact_id") == payload.get("summary", {}).get("artifact_id"),
                "harder_target_kept_support_only": harder_target.get("promotability") == "NOT_READY",
                "canonical_mutation_withheld": True,
            },
            "inputs": {
                "payload_artifact_id": payload.get("summary", {}).get("artifact_id"),
                "payload_artifact_pointer": payload.get("summary", {}).get("artifact_pointer"),
                "harder_target_artifact_id": harder_target.get("artifact_id"),
                "row_id": payload_binding.get("row_id"),
                "seam_id": payload_binding.get("seam_id"),
                "target_package_id": payload_binding.get("target_package_id"),
                "blocker_definition_id": active_definition.get("definition_id"),
                "promotion_ruling": active_definition.get("promotion_ruling"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "governed_decision": governed_decision,
            "target_row_id": payload_binding.get("row_id"),
            "target_seam_id": payload_binding.get("seam_id"),
            "target_package_id": payload_binding.get("target_package_id"),
            "primary_artifact_id": payload.get("summary", {}).get("artifact_id"),
            "supporting_artifact_id": harder_target.get("artifact_id"),
            "canonical_status_v0": "NONCANONICAL_UNLESS_EXPLICIT_GOVERNED_PROMOTION_PASS",
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "payload_record": _ptr(payload_path),
            "comparison_report": _ptr(comparison_path),
            "witness_binding": _ptr(witness_binding_path),
            "blocker_definitions": _ptr(blocker_definitions_path),
            "payload_requirements": _ptr(payload_requirements_path),
            "promotion_lane_policy": _ptr(promotion_policy_path),
            "canonical_mutation_protocol": _ptr(mutation_protocol_path),
        },
        "non_claim_boundary": "Repository-local governed intake wrapper only; no governed promotion pass, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT governed review wrapper report for the research-mode payload and comparison bundle.")
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
        "research_mode_qm_stat_governed_review_wrapper_report: "
        f"decision={payload['summary']['governed_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())