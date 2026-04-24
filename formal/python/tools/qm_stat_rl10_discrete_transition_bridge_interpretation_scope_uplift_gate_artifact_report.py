from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_20260422_v0.json"
)

_REQUIRED_TEXT_FIELDS = (
    "uplift_gate_artifact_id",
    "uplift_gate_artifact_question",
    "uplift_gate_run_mode",
    "uplift_gate_success_condition",
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
    policy = dict(declaration.get("uplift_gate_artifact_policy", {}))
    contract = dict(declaration.get("uplift_gate_artifact_contract", {}))

    evidence_report_path = REPO_ROOT / _norm(
        required_inputs.get("bridge_interpretation_scope_uplift_evidence_object_report")
    )
    evidence_report = _read_json(evidence_report_path)

    evidence_summary = dict(evidence_report.get("summary", {}))
    evidence_inputs = dict(dict(evidence_report.get("objective_quality", {})).get("inputs", {}))

    expected_comparator_id = _norm(seam_scope.get("external_comparator_id"))
    expected_quantity_id = _norm(seam_scope.get("bridge_quantity_id"))

    required_evidence_outcome = _norm(policy.get("required_evidence_object_outcome"))
    required_admissible_class = _norm(policy.get("required_admissible_evidence_class"))
    required_admissible_object_id = _norm(policy.get("required_admissible_evidence_object_id"))
    required_uplift_gate_id = _norm(policy.get("required_uplift_gate_id"))
    required_uplift_gate_contract = _norm(policy.get("required_uplift_gate_contract"))

    evidence_outcome = _norm(evidence_summary.get("review_outcome"))
    evidence_admissible_class = _norm(evidence_summary.get("admissible_evidence_class"))
    evidence_admissible_object_id = _norm(evidence_summary.get("admissible_evidence_object_id"))
    evidence_gate_id = _norm(evidence_inputs.get("uplift_gate_id"))
    evidence_gate_contract = _norm(evidence_inputs.get("uplift_gate_contract"))
    evidence_branch_reopened = bool(evidence_summary.get("branch_execution_reopened", True))

    evidence_outcome_matches = evidence_outcome == required_evidence_outcome
    admissible_class_matches = evidence_admissible_class == required_admissible_class
    admissible_object_id_matches = evidence_admissible_object_id == required_admissible_object_id
    uplift_gate_id_matches = evidence_gate_id == required_uplift_gate_id
    uplift_gate_contract_matches = evidence_gate_contract == required_uplift_gate_contract

    declared_text_fields_present = all(_norm(policy.get(field)) for field in _REQUIRED_TEXT_FIELDS)

    single_bounded_run_only = bool(policy.get("single_bounded_run_only", False))
    no_expansion_no_rollout_guard = bool(policy.get("no_expansion_no_rollout_guard", False))
    non_promotion_non_closure_boundary = bool(policy.get("non_promotion_non_closure_boundary", False))
    branch_execution_reopened = bool(policy.get("branch_execution_reopened", True))

    implicitly_authorizes_promotion = bool(policy.get("implicitly_authorizes_promotion", False))
    implicitly_authorizes_multi_lane_expansion = bool(policy.get("implicitly_authorizes_multi_lane_expansion", False))
    implicitly_authorizes_rollout = bool(policy.get("implicitly_authorizes_rollout", False))
    promotion_expansion_rollout_disallowed = (
        not implicitly_authorizes_promotion
        and not implicitly_authorizes_multi_lane_expansion
        and not implicitly_authorizes_rollout
    )

    evidence_comparator_id = _norm(evidence_summary.get("external_comparator_id"))
    evidence_quantity_id = _norm(evidence_summary.get("bridge_quantity_id"))
    scope_match = evidence_comparator_id == expected_comparator_id and evidence_quantity_id == expected_quantity_id

    declaration_valid = (
        evidence_outcome_matches
        and admissible_class_matches
        and admissible_object_id_matches
        and uplift_gate_id_matches
        and uplift_gate_contract_matches
        and declared_text_fields_present
        and single_bounded_run_only
        and no_expansion_no_rollout_guard
        and non_promotion_non_closure_boundary
        and promotion_expansion_rollout_disallowed
        and not evidence_branch_reopened
        and not branch_execution_reopened
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if not scope_match:
        review_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_SCOPE_VIOLATION"
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif declaration_valid:
        review_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_DECLARED_AND_SINGLE_RUN_READY"
        next_action = "AUTHOR_SINGLE_BOUNDED_UPLIFT_GATE_EXECUTION_PACKET_WITHOUT_BRANCH_REOPEN"
    else:
        review_outcome = "INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_DECLARATION_INVALID"
        next_action = "REPAIR_UPLIFT_GATE_ARTIFACT_DECLARATION_AND_RECHECK"

    if review_outcome not in allowed_outcomes:
        review_outcome = _norm(
            contract.get("default_outcome", "INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_DECLARATION_INVALID")
        )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "evidence_object_outcome_matches_required": evidence_outcome_matches,
            "admissible_evidence_class_matches": admissible_class_matches,
            "admissible_evidence_object_id_matches": admissible_object_id_matches,
            "uplift_gate_id_matches": uplift_gate_id_matches,
            "uplift_gate_contract_matches": uplift_gate_contract_matches,
            "declared_text_fields_present": declared_text_fields_present,
            "single_bounded_run_only": single_bounded_run_only,
            "no_expansion_no_rollout_guard": no_expansion_no_rollout_guard,
            "non_promotion_non_closure_boundary": non_promotion_non_closure_boundary,
            "promotion_expansion_rollout_disallowed": promotion_expansion_rollout_disallowed,
            "evidence_branch_execution_reopened_is_false": not evidence_branch_reopened,
            "branch_execution_reopened_is_false": not branch_execution_reopened,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": _norm(contract.get("no_loop_rule"))
            == "DECLARATION_ONLY_NO_EXECUTION_REOPEN_IN_THIS_PACKET",
            "single_terminal_outcome_rule_declared": _norm(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_UPLIFT_GATE_ARTIFACT_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "declaration_valid": declaration_valid and scope_match,
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "uplift_gate_artifact_question_answered": True,
            },
            "inputs": {
                "required_evidence_object_outcome": required_evidence_outcome,
                "observed_evidence_object_outcome": evidence_outcome,
                "required_admissible_evidence_class": required_admissible_class,
                "observed_admissible_evidence_class": evidence_admissible_class,
                "required_admissible_evidence_object_id": required_admissible_object_id,
                "observed_admissible_evidence_object_id": evidence_admissible_object_id,
                "required_uplift_gate_id": required_uplift_gate_id,
                "observed_uplift_gate_id": evidence_gate_id,
                "required_uplift_gate_contract": required_uplift_gate_contract,
                "observed_uplift_gate_contract": evidence_gate_contract,
                "uplift_gate_artifact_id": _norm(policy.get("uplift_gate_artifact_id")),
                "uplift_gate_artifact_question": _norm(policy.get("uplift_gate_artifact_question")),
                "uplift_gate_run_mode": _norm(policy.get("uplift_gate_run_mode")),
                "uplift_gate_success_condition": _norm(policy.get("uplift_gate_success_condition")),
                "falsification_condition": _norm(policy.get("falsification_condition")),
                "stop_condition_if_not_met": _norm(policy.get("stop_condition_if_not_met")),
            },
            "summary": {
                "all_criteria_satisfied": (declaration_valid and scope_match)
                and (review_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "uplift_gate_artifact_id": _norm(policy.get("uplift_gate_artifact_id")),
            "admissible_evidence_class": required_admissible_class,
            "admissible_evidence_object_id": required_admissible_object_id,
            "branch_execution_reopened": False,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_interpretation_scope_uplift_evidence_object_report": _ptr(evidence_report_path),
        },
        "non_claim_boundary": "Repository-local interpretation-scope uplift gate artifact declaration report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge interpretation-scope uplift gate artifact declaration report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_artifact_20260422_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_gate_artifact_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
