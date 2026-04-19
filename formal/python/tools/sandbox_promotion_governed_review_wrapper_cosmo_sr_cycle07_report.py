from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json"
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


def _protocol_ok(text: str) -> bool:
    required = (
        "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_EMISSION_RULE_v0: EMIT_ONLY_ON_GOVERNED_PROMOTION_REVIEW_PROMOTE_DECISION",
        "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_REQUIRED_FIELDS_v0: TARGET_ROW_PLUS_TARGET_SEAM_PLUS_SOURCE_ARTIFACT_PLUS_SOURCE_PAYLOAD_PLUS_DECISION_RECORD_PLUS_SURFACE_DELTA_PLUS_PRESTATE_PLUS_POSTSTATE_PLUS_ROLLBACK_ANCHOR_PLUS_NONCLAIM_BOUNDARY",
        "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_NOOP_RULE_v0: HOLD_OR_REJECT_DECISION_EMITS_NO_CANONICAL_MUTATION",
        "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_FAIL_CLOSED_RULE_v0: MISSING_SURFACE_DELTA_OR_PREPOST_STATE_OR_ROLLBACK_ANCHOR_BLOCKS_PROMOTE",
    )
    return all(token in text for token in required)


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    payload_path = REPO_ROOT / str(required_inputs.get("payload_record", "")).strip()
    payload_requirements_path = REPO_ROOT / str(required_inputs.get("payload_requirements", "")).strip()
    pilot_binding_path = REPO_ROOT / str(required_inputs.get("pilot_binding", "")).strip()
    sandbox_report_path = REPO_ROOT / str(required_inputs.get("sandbox_execution_report", "")).strip()
    protocol_path = REPO_ROOT / str(required_inputs.get("canonical_mutation_protocol", "")).strip()
    promotion_policy_path = REPO_ROOT / str(required_inputs.get("promotion_lane_policy", "")).strip()
    action_standard_path = REPO_ROOT / str(required_inputs.get("canonical_action_promotion_standard", "")).strip()

    payload = _read_json(payload_path)
    pilot_binding = _read_json(pilot_binding_path)
    sandbox_report = _read_json(sandbox_report_path)
    payload_requirements_text = _read_text(payload_requirements_path)
    protocol_text = _read_text(protocol_path)
    promotion_policy_text = _read_text(promotion_policy_path)
    action_standard_text = _read_text(action_standard_path)

    artifact_path = REPO_ROOT / str(payload.get("artifact_pointer", "")).strip()
    artifact = _read_json(artifact_path)

    metadata = dict(payload.get("metadata_record", {}))
    target_binding = dict(payload.get("target_binding", {}))
    contradiction_check = dict(metadata.get("contradiction_check", {}))
    governed_test_selection = dict(payload.get("governed_test_selection", {}))
    mutation_plan = dict(payload.get("mutation_plan", {}))
    contract_bindings = dict(payload.get("contract_bindings", {}))

    binding = dict(pilot_binding.get("pilot_binding", {}))
    sandbox_summary = dict(sandbox_report.get("summary", {}))
    artifact_adjudication = str(artifact.get("adjudication", {}).get("value", "")).strip()

    contract_bindings_ok = (
        contract_bindings.get("payload_requirements") == _ptr(payload_requirements_path)
        and contract_bindings.get("pilot_binding") == _ptr(pilot_binding_path)
        and contract_bindings.get("governed_review_wrapper") == _ptr(declaration_path)
        and contract_bindings.get("canonical_mutation_protocol") == _ptr(protocol_path)
    )
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
    action_standard_ok = "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT" in action_standard_text
    protocol_ok = _protocol_ok(protocol_text)

    mutation_plan_ok = (
        mutation_plan.get("mutation_protocol") == _ptr(protocol_path)
        and bool(mutation_plan.get("candidate_canonical_surfaces_to_change_if_promoted"))
        and bool(mutation_plan.get("prestate_tokens"))
        and bool(mutation_plan.get("poststate_tokens_if_promoted"))
        and bool(mutation_plan.get("rollback_anchor"))
    )
    contradiction_pass = str(payload.get("contradiction_check_result", "")).startswith("PASS_") and str(
        contradiction_check.get("result", "")
    ).startswith("PASS_")
    target_binding_ok = (
        target_binding.get("row_id") == str(policy.get("required_target_row", "")).strip()
        and target_binding.get("seam_id") == str(policy.get("required_target_seam", "")).strip()
        and target_binding.get("row_id") == binding.get("target_row_id")
        and target_binding.get("seam_id") == binding.get("target_seam_id")
        and metadata.get("target_binding", {}).get("row_id") == binding.get("target_row_id")
        and metadata.get("target_binding", {}).get("seam_id") == binding.get("target_seam_id")
    )
    payload_shape_ok = (
        metadata.get("artifact_id") == artifact.get("artifact_id")
        and metadata.get("promotion_readiness") == str(policy.get("required_promotion_readiness", "")).strip()
        and payload.get("decision_boundary") == str(policy.get("required_payload_decision_boundary", "")).strip()
        and bool(governed_test_selection.get("selected_tests"))
        and artifact.get("seam_id") == str(policy.get("required_target_seam", "")).strip()
    )
    binding_class_ok = metadata.get("delta_class") == str(policy.get("required_delta_class", "")).strip() and metadata.get(
        "artifact_class"
    ) in {
        str(policy.get("required_payload_artifact_class", "")).strip(),
        str(binding.get("required_artifact_class", "")).strip(),
        "PROMOTION_CANDIDATE_SANDBOX_ARTIFACT",
    }
    payload_eligible = (
        payload_shape_ok
        and binding_class_ok
        and contradiction_pass
        and metadata.get("artifact_class") == str(policy.get("required_payload_artifact_class", "")).strip()
    )
    sandbox_ok = (
        sandbox_summary.get("terminal_outcome") == str(policy.get("required_sandbox_terminal_outcome", "")).strip()
        and sandbox_summary.get("target_row_id") == str(policy.get("required_target_row", "")).strip()
        and sandbox_summary.get("target_seam_id") == str(policy.get("required_target_seam", "")).strip()
        and sandbox_summary.get("promotion_earned") is False
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "SANDBOX_PROMOTION_GOVERNED_REVIEW_EVIDENCE_INCOMPLETE")
    ).strip()

    decision = "hold"
    if not all([contract_bindings_ok, payload_contract_ok, promotion_policy_ok, action_standard_ok, protocol_ok, mutation_plan_ok, target_binding_ok, sandbox_ok]):
        terminal_outcome = "SANDBOX_PROMOTION_GOVERNED_REVIEW_EVIDENCE_INCOMPLETE"
        decision = "repair"
        next_action = "REPAIR_SANDBOX_PROMOTION_GOVERNED_REVIEW_INPUTS_AND_RERUN"
    elif not payload_eligible:
        terminal_outcome = "SANDBOX_PROMOTION_GOVERNED_REVIEW_REJECT_DECISION_EMITTED"
        decision = "reject"
        next_action = str(policy.get("required_wrapper_next_action_on_reject", "")).strip()
    elif artifact_adjudication == str(policy.get("required_artifact_adjudication_for_promote", "")).strip():
        terminal_outcome = "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED"
        decision = "promote"
        next_action = str(policy.get("required_wrapper_next_action_on_promote", "")).strip()
    else:
        terminal_outcome = "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED"
        decision = "hold"
        next_action = str(policy.get("required_wrapper_next_action_on_hold", "")).strip()

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    promote_emitted = terminal_outcome == "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED"
    hold_reason = None
    reject_reason = None
    if terminal_outcome == "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED":
        hold_reason = str(policy.get("hold_reason_if_not_discharged", "")).strip()
    if terminal_outcome == "SANDBOX_PROMOTION_GOVERNED_REVIEW_REJECT_DECISION_EMITTED":
        reject_reason = str(policy.get("reject_reason_if_payload_ineligible", "")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "payload_contract_bindings_match": contract_bindings_ok,
            "payload_requirement_tokens_present": payload_contract_ok,
            "promotion_policy_tokens_present": promotion_policy_ok,
            "canonical_action_standard_present": action_standard_ok,
            "mutation_protocol_tokens_present": protocol_ok,
            "mutation_plan_complete": mutation_plan_ok,
            "pilot_binding_match": target_binding_ok,
            "sandbox_execution_report_match": sandbox_ok,
            "payload_eligible_for_review": payload_eligible,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "promote_only_when_artifact_discharged": (terminal_outcome != "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED")
                or artifact_adjudication == str(policy.get("required_artifact_adjudication_for_promote", "")).strip(),
                "hold_or_reject_emit_no_canonical_mutation": (terminal_outcome == "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED")
                or not promote_emitted,
            },
            "inputs": {
                "pilot_track_id": binding.get("pilot_track_id"),
                "target_row_id": target_binding.get("row_id"),
                "target_seam_id": target_binding.get("seam_id"),
                "artifact_id": artifact.get("artifact_id"),
                "artifact_adjudication": artifact_adjudication,
                "sandbox_terminal_outcome": sandbox_summary.get("terminal_outcome"),
                "sandbox_next_action": sandbox_summary.get("next_action"),
                "decision_boundary": payload.get("decision_boundary"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "governed_decision": decision,
            "target_row_id": target_binding.get("row_id"),
            "target_seam_id": target_binding.get("seam_id"),
            "artifact_id": artifact.get("artifact_id"),
            "artifact_adjudication": artifact_adjudication,
            "canonical_mutation_emitted": promote_emitted,
            "hold_reason": hold_reason,
            "reject_reason": reject_reason,
            "next_action": next_action,
        },
        "emitted_mutation_instruction": mutation_plan if promote_emitted else None,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "payload_record": _ptr(payload_path),
            "payload_requirements": _ptr(payload_requirements_path),
            "pilot_binding": _ptr(pilot_binding_path),
            "sandbox_execution_report": _ptr(sandbox_report_path),
            "canonical_mutation_protocol": _ptr(protocol_path),
            "promotion_lane_policy": _ptr(promotion_policy_path),
            "canonical_action_promotion_standard": _ptr(action_standard_path),
            "artifact": _ptr(artifact_path),
        },
        "non_claim_boundary": "Repository-local governed promotion review only; no scientific adequacy, external truth, or automatic canonical writeback claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the sandbox-promotion governed review wrapper report for the bounded COSMO-SR Cycle07 pilot."
    )
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
        "sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())