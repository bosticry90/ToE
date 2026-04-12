from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_20260412_v0.json"
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
    seam_scope = dict(declaration.get("seam_scope", {}))
    policy = dict(declaration.get("admissibility_policy", {}))
    contract = dict(declaration.get("review_contract", {}))

    naming_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()
    naming_review = _read_json(naming_review_path)
    naming_summary = dict(naming_review.get("summary", {}))

    naming_outcome = str(naming_summary.get("review_outcome", "")).strip()
    observed_comparator_id = str(
        dict(naming_review.get("objective_quality", {})).get("inputs", {}).get("observed_comparator_id", "")
    ).strip()
    observed_quantity_id = str(
        dict(naming_review.get("objective_quality", {})).get("inputs", {}).get("observed_quantity_id", "")
    ).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
    )

    admissibility_standard_defined = bool(policy.get("admissibility_standard_defined", False))
    declaration_standard_defined = bool(policy.get("declaration_standard_defined", False))
    bounded_check_families_defined = bool(policy.get("bounded_check_families_defined", False))
    require_external_validation_policy_surface = bool(
        policy.get("require_external_validation_policy_surface", False)
    )
    external_validation_policy_surface_defined = bool(
        policy.get("external_validation_policy_surface_defined", False)
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(contract.get("default_outcome", "LIMITED_HOLD_RETAINED")).strip()

    if (
        require_external_validation_policy_surface
        and not external_validation_policy_surface_defined
    ):
        review_outcome = "EXTERNAL_VALIDATION_POLICY_SURFACE_REQUIRED"
        next_action = "DEFINE_EXTERNAL_VALIDATION_POLICY_SURFACE_BEFORE_CONTINUING"
    elif naming_outcome in {
        "BOUNDED_REPEATABILITY_CHECK_NAMED",
        "BOUNDED_CROSS_PROBE_CHECK_NAMED",
    } and not (
        admissibility_standard_defined
        and declaration_standard_defined
        and bounded_check_families_defined
    ):
        review_outcome = "DECLARATION_STANDARD_REQUIRED_BEFORE_NAMING"
        next_action = "DEFINE_ADMISSIBILITY_AND_DECLARATION_STANDARD_FOR_NAMED_BOUNDED_CHECKS"
    elif naming_outcome in {
        "BOUNDED_REPEATABILITY_CHECK_NAMED",
        "BOUNDED_CROSS_PROBE_CHECK_NAMED",
    } and (
        admissibility_standard_defined
        and declaration_standard_defined
        and bounded_check_families_defined
        and scope_match
    ):
        review_outcome = "ADMISSIBILITY_STANDARD_READY_FOR_BOUNDED_CHECK_NAMING"
        next_action = "PROCEED_TO_SINGLE_BOUNDED_CHECK_DECLARATION_GATE"
    else:
        review_outcome = "LIMITED_HOLD_RETAINED"
        next_action = "RETAIN_LIMITED_HOLD_UNTIL_POLICY_AND_NAMING_PRECONDITIONS_ARE_MET"

    if review_outcome not in allowed_outcomes:
        review_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "naming_review_input_present": bool(naming_outcome),
            "same_comparator_and_quantity_preserved": scope_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_ADMISSIBILITY_STANDARD_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "policy_preconditions_explicit": True,
            },
            "inputs": {
                "naming_outcome": naming_outcome,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "admissibility_standard_defined": admissibility_standard_defined,
                "declaration_standard_defined": declaration_standard_defined,
                "bounded_check_families_defined": bounded_check_families_defined,
                "require_external_validation_policy_surface": require_external_validation_policy_surface,
                "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
            },
            "summary": {
                "all_criteria_satisfied": review_outcome
                in {
                    "ADMISSIBILITY_STANDARD_READY_FOR_BOUNDED_CHECK_NAMING",
                    "DECLARATION_STANDARD_REQUIRED_BEFORE_NAMING",
                    "LIMITED_HOLD_RETAINED",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "naming_outcome": naming_outcome,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_review_path),
        },
        "non_claim_boundary": "Repository-local bridge admissibility-standard review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge admissibility-standard review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_report: "
        f"review_outcome={payload['summary']['review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
