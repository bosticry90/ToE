from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_RESTART_HIGHER_LEVEL_POLICY_TRIGGER_REPORT_20260413_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_RESTART_HIGHER_LEVEL_POLICY_TRIGGER_20260413_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("higher_level_policy_trigger_contract", {}))
    outcome_contract = dict(declaration.get("higher_level_policy_trigger_outcome_contract", {}))

    frontier_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_preservation_record_report", "")
    ).strip()
    review_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()
    policy_standard_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_standard_formalization_report", "")
    ).strip()

    frontier = _read_json(frontier_path)
    review = _read_json(review_path)
    policy_standard = _read_json(policy_standard_path)

    frontier_summary = dict(frontier.get("summary", {}))
    frontier_state = dict(frontier.get("frontier_state", {}))
    review_summary = dict(review.get("summary", {}))
    policy_standard_summary = dict(policy_standard.get("summary", {}))

    frontier_outcome = str(frontier_summary.get("terminal_outcome", "")).strip()
    frontier_next_action = str(frontier_summary.get("next_action", "")).strip()
    restart_conditions = list(frontier_state.get("restart_conditions", []))
    policy_review_outcome = str(review_summary.get("review_outcome", "")).strip()
    policy_standard_formalization_outcome = str(
        policy_standard_summary.get("terminal_outcome", "")
    ).strip()
    policy_standard_defined = bool(policy_standard_summary.get("policy_standard_defined", False))
    policy_standard_approved = bool(policy_standard_summary.get("policy_standard_approved", False))

    required_frontier_preservation_outcome = str(
        contract.get("required_frontier_preservation_outcome", "")
    ).strip()
    required_frontier_next_action = str(contract.get("required_frontier_next_action", "")).strip()
    required_restart_condition_token = str(contract.get("required_restart_condition_token", "")).strip()
    required_policy_standard_formalization_outcome = str(
        contract.get("required_policy_standard_formalization_outcome", "")
    ).strip()
    required_policy_standard_approved = bool(contract.get("required_policy_standard_approved", False))
    allowed_policy_review_outcomes_for_authorization = set(
        contract.get("allowed_policy_review_outcomes_for_authorization", [])
    )
    require_policy_standard_defined = bool(contract.get("require_policy_standard_defined", False))

    contract_shape_ok = all(
        key in contract
        for key in [
            "required_frontier_preservation_outcome",
            "required_frontier_next_action",
            "required_restart_condition_token",
            "required_policy_standard_formalization_outcome",
            "required_policy_standard_approved",
            "allowed_policy_review_outcomes_for_authorization",
            "require_policy_standard_defined",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    frontier_preconditions_ok = (
        frontier_outcome == required_frontier_preservation_outcome
        and frontier_next_action == required_frontier_next_action
        and required_restart_condition_token in restart_conditions
        and policy_standard_formalization_outcome == required_policy_standard_formalization_outcome
        and policy_standard_approved == required_policy_standard_approved
    )
    policy_review_supports_authorization = (
        policy_review_outcome in allowed_policy_review_outcomes_for_authorization
    )
    authorization_ready = frontier_preconditions_ok and policy_review_supports_authorization and (
        policy_standard_approved and (policy_standard_defined or not require_policy_standard_defined)
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "HIGHER_LEVEL_POLICY_REVISION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not contract_shape_ok:
        terminal_outcome = "HOLD_PENDING_HIGHER_LEVEL_POLICY_REVISION_REPAIR"
        next_action = "REPAIR_HIGHER_LEVEL_POLICY_TRIGGER_CONTRACT_SHAPE"
    elif not frontier_preconditions_ok:
        terminal_outcome = "HIGHER_LEVEL_POLICY_REVISION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_FRONTIER_PRECONDITIONS_BEFORE_POLICY_TRIGGER_REVIEW"
    elif authorization_ready:
        terminal_outcome = "HIGHER_LEVEL_POLICY_REVISION_AUTHORIZED"
        next_action = "SURFACE_HIGHER_LEVEL_POLICY_REVISION_TO_RESTART_TRIGGER_CONTRACT"
    else:
        terminal_outcome = "HIGHER_LEVEL_POLICY_REVISION_NOT_AUTHORIZED"
        next_action = "RETAIN_GOVERNED_STOP_STATE_UNTIL_HIGHER_LEVEL_POLICY_STANDARD_IS_DEFINED"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "frontier_preservation_outcome_match": frontier_outcome == required_frontier_preservation_outcome,
            "frontier_next_action_match": frontier_next_action == required_frontier_next_action,
            "required_restart_condition_present": required_restart_condition_token in restart_conditions,
            "policy_standard_formalization_outcome_match": policy_standard_formalization_outcome
            == required_policy_standard_formalization_outcome,
            "policy_review_supports_authorization": policy_review_supports_authorization,
            "policy_standard_defined": policy_standard_defined,
            "policy_standard_approved": policy_standard_approved == required_policy_standard_approved,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_HIGHER_LEVEL_POLICY_TRIGGER_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_HIGHER_LEVEL_POLICY_TRIGGER_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "higher_level_policy_trigger_preconditions_satisfied": frontier_preconditions_ok,
            },
            "inputs": {
                "frontier_preservation_outcome": frontier_outcome,
                "required_frontier_preservation_outcome": required_frontier_preservation_outcome,
                "frontier_next_action": frontier_next_action,
                "required_frontier_next_action": required_frontier_next_action,
                "restart_conditions": restart_conditions,
                "required_restart_condition_token": required_restart_condition_token,
                "policy_review_outcome": policy_review_outcome,
                "policy_standard_formalization_outcome": policy_standard_formalization_outcome,
                "required_policy_standard_formalization_outcome": required_policy_standard_formalization_outcome,
                "allowed_policy_review_outcomes_for_authorization": sorted(
                    allowed_policy_review_outcomes_for_authorization
                ),
                "policy_standard_defined": policy_standard_defined,
                "policy_standard_approved": policy_standard_approved,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "trigger_family": "HIGHER_LEVEL_POLICY_OR_EVIDENCE_STANDARD",
            "higher_level_policy_revision_authorized": authorization_ready,
            "policy_review_outcome": policy_review_outcome,
            "policy_standard_formalization_outcome": policy_standard_formalization_outcome,
            "policy_standard_defined": policy_standard_defined,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_frontier_preservation_record_report": _ptr(frontier_path),
            "bridge_external_validation_policy_review_report": _ptr(review_path),
            "bridge_external_validation_policy_standard_formalization_report": _ptr(policy_standard_path),
        },
        "non_claim_boundary": "Repository-local higher-level policy restart trigger report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate higher-level policy restart trigger report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_restart_higher_level_policy_trigger_20260413_v0.json",
    )
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
        "science_restart_higher_level_policy_trigger_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())