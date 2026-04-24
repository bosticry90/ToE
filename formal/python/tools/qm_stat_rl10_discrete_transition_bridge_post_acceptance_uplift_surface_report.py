from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_20260422_v0.json"
)


_REQUIRED_TEXT_FIELDS = (
    "admissible_evidence_class",
    "admissible_evidence_object_id",
    "admissible_evidence_object_report",
    "uplift_trigger_condition",
    "uplift_success_condition",
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


def _normalized_string(value: Any) -> str:
    return str(value or "").strip()


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    seam_scope = dict(declaration.get("seam_scope", {}))
    policy = dict(declaration.get("uplift_surface_policy", {}))
    contract = dict(declaration.get("uplift_surface_contract", {}))

    normalization_path = REPO_ROOT / _normalized_string(
        required_inputs.get("bridge_limitation_mapping_normalization_review_report")
    )
    acceptance_path = REPO_ROOT / _normalized_string(
        required_inputs.get("bridge_signal_margin_limitation_acceptance_review_report")
    )

    normalization = _read_json(normalization_path)
    acceptance = _read_json(acceptance_path)

    normalization_summary = dict(normalization.get("summary", {}))
    acceptance_summary = dict(acceptance.get("summary", {}))

    expected_comparator_id = _normalized_string(seam_scope.get("external_comparator_id"))
    expected_quantity_id = _normalized_string(seam_scope.get("bridge_quantity_id"))

    required_normalization_outcome = _normalized_string(
        policy.get("required_normalization_outcome")
    )
    required_acceptance_outcome = _normalized_string(
        policy.get("required_acceptance_outcome")
    )

    normalization_outcome = _normalized_string(normalization_summary.get("review_outcome"))
    acceptance_outcome = _normalized_string(acceptance_summary.get("review_outcome"))

    normalization_outcome_matches = normalization_outcome == required_normalization_outcome
    acceptance_outcome_matches = acceptance_outcome == required_acceptance_outcome

    normalization_comparator_id = _normalized_string(
        normalization_summary.get("external_comparator_id")
    )
    normalization_quantity_id = _normalized_string(
        normalization_summary.get("bridge_quantity_id")
    )
    acceptance_comparator_id = _normalized_string(acceptance_summary.get("external_comparator_id"))
    acceptance_quantity_id = _normalized_string(acceptance_summary.get("bridge_quantity_id"))

    scope_match = (
        normalization_comparator_id == expected_comparator_id
        and normalization_quantity_id == expected_quantity_id
        and acceptance_comparator_id == expected_comparator_id
        and acceptance_quantity_id == expected_quantity_id
    )

    declaration_text_fields_present = all(_normalized_string(policy.get(key)) for key in _REQUIRED_TEXT_FIELDS)

    single_bounded_execution_object_only = bool(policy.get("single_bounded_execution_object_only", False))
    no_expansion_no_rollout_guard = bool(policy.get("no_expansion_no_rollout_guard", False))
    non_promotion_non_closure_boundary = bool(policy.get("non_promotion_non_closure_boundary", False))

    implicitly_authorizes_promotion = bool(policy.get("implicitly_authorizes_promotion", False))
    implicitly_authorizes_multi_lane_expansion = bool(
        policy.get("implicitly_authorizes_multi_lane_expansion", False)
    )
    implicitly_authorizes_rollout = bool(policy.get("implicitly_authorizes_rollout", False))

    promotion_expansion_rollout_disallowed = (
        not implicitly_authorizes_promotion
        and not implicitly_authorizes_multi_lane_expansion
        and not implicitly_authorizes_rollout
    )

    evidence_object_report_path = _normalized_string(policy.get("admissible_evidence_object_report"))
    evidence_object_report_named = evidence_object_report_path.endswith(".json")

    declaration_valid = (
        normalization_outcome_matches
        and acceptance_outcome_matches
        and declaration_text_fields_present
        and single_bounded_execution_object_only
        and no_expansion_no_rollout_guard
        and non_promotion_non_closure_boundary
        and promotion_expansion_rollout_disallowed
        and evidence_object_report_named
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        review_outcome = "POST_ACCEPTANCE_UPLIFT_SURFACE_SCOPE_VIOLATION"
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif declaration_valid:
        review_outcome = "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_READY_FOR_BOUNDED_EVIDENCE_OBJECT"
        next_action = "AUTHOR_AND_GATE_DECLARED_EVIDENCE_OBJECT_ONCE"
    else:
        review_outcome = "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID"
        next_action = "REPAIR_UPLIFT_SURFACE_DECLARATION_AND_RECHECK_GATE"

    if review_outcome not in allowed_outcomes:
        review_outcome = _normalized_string(
            contract.get("default_outcome", "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID")
        )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "normalization_outcome_matches_required": normalization_outcome_matches,
            "acceptance_outcome_matches_required": acceptance_outcome_matches,
            "declaration_text_fields_present": declaration_text_fields_present,
            "single_bounded_execution_object_only": single_bounded_execution_object_only,
            "no_expansion_no_rollout_guard": no_expansion_no_rollout_guard,
            "non_promotion_non_closure_boundary": non_promotion_non_closure_boundary,
            "promotion_expansion_rollout_disallowed": promotion_expansion_rollout_disallowed,
            "evidence_object_report_named": evidence_object_report_named,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": _normalized_string(contract.get("no_loop_rule"))
            == "DECLARATION_ONLY_NO_EXECUTION_WITHIN_THIS_SURFACE",
            "single_terminal_outcome_rule_declared": _normalized_string(
                contract.get("single_terminal_outcome_rule")
            )
            == "EXACTLY_ONE_ALLOWED_POST_ACCEPTANCE_UPLIFT_SURFACE_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "declaration_valid": declaration_valid and scope_match,
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "uplift_surface_question_answered": True,
            },
            "inputs": {
                "required_normalization_outcome": required_normalization_outcome,
                "observed_normalization_outcome": normalization_outcome,
                "required_acceptance_outcome": required_acceptance_outcome,
                "observed_acceptance_outcome": acceptance_outcome,
                "admissible_evidence_class": _normalized_string(policy.get("admissible_evidence_class")),
                "admissible_evidence_object_id": _normalized_string(
                    policy.get("admissible_evidence_object_id")
                ),
                "admissible_evidence_object_report": evidence_object_report_path,
                "uplift_trigger_condition": _normalized_string(policy.get("uplift_trigger_condition")),
                "uplift_success_condition": _normalized_string(policy.get("uplift_success_condition")),
                "falsification_condition": _normalized_string(policy.get("falsification_condition")),
                "stop_condition_if_not_met": _normalized_string(policy.get("stop_condition_if_not_met")),
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_normalization_comparator_id": normalization_comparator_id,
                "observed_normalization_quantity_id": normalization_quantity_id,
                "observed_acceptance_comparator_id": acceptance_comparator_id,
                "observed_acceptance_quantity_id": acceptance_quantity_id,
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
            "single_bounded_execution_object_only": single_bounded_execution_object_only,
            "no_expansion_no_rollout_guard": no_expansion_no_rollout_guard,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_limitation_mapping_normalization_review_report": _ptr(normalization_path),
            "bridge_signal_margin_limitation_acceptance_review_report": _ptr(acceptance_path),
        },
        "non_claim_boundary": "Repository-local post-acceptance uplift surface declaration report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge post-acceptance uplift surface declaration report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_post_acceptance_uplift_surface_20260422_v0.json",
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
    print("qm_stat_rl10_discrete_transition_bridge_post_acceptance_uplift_surface_report: " f"{out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
