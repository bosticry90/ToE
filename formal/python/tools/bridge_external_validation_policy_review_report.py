from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BRIDGE_EXTERNAL_VALIDATION_POLICY_REVIEW_20260412_v0.json"
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
    policy = dict(declaration.get("external_validation_policy", {}))
    contract = dict(declaration.get("review_contract", {}))

    admissibility_path = REPO_ROOT / str(
        required_inputs.get("bridge_admissibility_standard_review_report", "")
    ).strip()
    naming_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()
    minimum_evidence_path = REPO_ROOT / str(
        required_inputs.get("bridge_minimum_second_cycle_evidence_object_report", "")
    ).strip()
    material_repeatability_criteria_path = REPO_ROOT / str(
        required_inputs.get("bridge_material_repeatability_admissibility_criteria_report", "")
    ).strip()
    approval_eligible_review_outcome_path = REPO_ROOT / str(
        required_inputs.get("bridge_approval_eligible_policy_review_outcome_report", "")
    ).strip()

    admissibility = _read_json(admissibility_path)
    naming = _read_json(naming_path)
    minimum_evidence = _read_json(minimum_evidence_path)
    material_repeatability_criteria = _read_json(material_repeatability_criteria_path)
    approval_eligible_review_outcome = _read_json(approval_eligible_review_outcome_path)

    admissibility_summary = dict(admissibility.get("summary", {}))
    admissibility_inputs = dict(dict(admissibility.get("objective_quality", {})).get("inputs", {}))
    naming_summary = dict(naming.get("summary", {}))
    naming_inputs = dict(dict(naming.get("objective_quality", {})).get("inputs", {}))
    minimum_evidence_summary = dict(minimum_evidence.get("summary", {}))
    material_repeatability_criteria_summary = dict(material_repeatability_criteria.get("summary", {}))
    approval_eligible_review_outcome_summary = dict(approval_eligible_review_outcome.get("summary", {}))

    admissibility_outcome = str(admissibility_summary.get("review_outcome", "")).strip()
    naming_outcome = str(naming_summary.get("review_outcome", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    observed_comparator_id = str(admissibility_inputs.get("observed_comparator_id", "")).strip()
    observed_quantity_id = str(admissibility_inputs.get("observed_quantity_id", "")).strip()
    naming_observed_comparator_id = str(naming_inputs.get("observed_comparator_id", "")).strip()
    naming_observed_quantity_id = str(naming_inputs.get("observed_quantity_id", "")).strip()

    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
        and naming_observed_comparator_id == expected_comparator_id
        and naming_observed_quantity_id == expected_quantity_id
    )

    repeatability_criteria_defined = bool(
        policy.get("repeatability_admissibility_criteria_defined", False)
        or material_repeatability_criteria_summary.get("repeatability_admissibility_criteria_defined", False)
    )
    approval_eligible_repeatability_review_outcome_defined = bool(
        policy.get("approval_eligible_repeatability_review_outcome_defined", False)
        or approval_eligible_review_outcome_summary.get(
            "approval_eligible_repeatability_review_outcome_defined", False
        )
    )
    cross_probe_criteria_defined = bool(policy.get("cross_probe_admissibility_criteria_defined", False))
    second_cycle_minimum_evidence_defined = bool(
        policy.get("second_cycle_minimum_evidence_defined", False)
        or minimum_evidence_summary.get("second_cycle_minimum_evidence_defined", False)
    )
    second_cycle_minimum_evidence_satisfied = bool(
        policy.get("second_cycle_minimum_evidence_satisfied", False)
        or minimum_evidence_summary.get("second_cycle_minimum_evidence_satisfied", False)
    )
    no_further_external_validation_path_triggered = bool(
        policy.get("no_further_external_validation_path_triggered", False)
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(contract.get("default_outcome", "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD")).strip()

    if no_further_external_validation_path_triggered or not scope_match:
        review_outcome = "NO_FURTHER_EXTERNAL_VALIDATION_PATH_JUSTIFIED_YET"
        next_action = "RETAIN_HOLD_AND_DO_NOT_OPEN_NEW_EXTERNAL_VALIDATION_PATH"
    elif (
        repeatability_criteria_defined
        and approval_eligible_repeatability_review_outcome_defined
        and admissibility_outcome in {
            "ADMISSIBILITY_STANDARD_READY_FOR_BOUNDED_CHECK_NAMING",
            "LIMITED_HOLD_RETAINED",
        }
        and naming_outcome in {
            "BOUNDED_REPEATABILITY_CHECK_NAMED",
            "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
        }
    ):
        review_outcome = "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED"
        next_action = "ALLOW_ONLY_NAMED_BOUNDED_REPEATABILITY_CHECK_GATE_REVIEW"
    elif (
        cross_probe_criteria_defined
        and second_cycle_minimum_evidence_defined
        and second_cycle_minimum_evidence_satisfied
        and admissibility_outcome in {
            "ADMISSIBILITY_STANDARD_READY_FOR_BOUNDED_CHECK_NAMING",
            "LIMITED_HOLD_RETAINED",
        }
        and naming_outcome in {
            "BOUNDED_CROSS_PROBE_CHECK_NAMED",
            "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
        }
    ):
        review_outcome = "ADMISSIBLE_CROSS_PROBE_STANDARD_DEFINED"
        next_action = "ALLOW_ONLY_NAMED_BOUNDED_CROSS_PROBE_CHECK_GATE_REVIEW"
    else:
        review_outcome = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"
        next_action = "RETAIN_LIMITED_HOLD_UNTIL_EXTERNAL_VALIDATION_POLICY_PRECONDITIONS_ARE_DEFINED"

    if review_outcome not in allowed_outcomes:
        review_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "admissibility_input_present": bool(admissibility_outcome),
            "naming_input_present": bool(naming_outcome),
            "same_comparator_and_quantity_preserved": scope_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_EXTERNAL_VALIDATION_POLICY_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_EXTERNAL_VALIDATION_POLICY_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "policy_prerequisites_explicit": True,
            },
            "inputs": {
                "admissibility_outcome": admissibility_outcome,
                "naming_outcome": naming_outcome,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "naming_observed_comparator_id": naming_observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "naming_observed_quantity_id": naming_observed_quantity_id,
                "repeatability_admissibility_criteria_defined": repeatability_criteria_defined,
                "approval_eligible_repeatability_review_outcome_defined": approval_eligible_repeatability_review_outcome_defined,
                "cross_probe_admissibility_criteria_defined": cross_probe_criteria_defined,
                "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
                "second_cycle_minimum_evidence_satisfied": second_cycle_minimum_evidence_satisfied,
                "minimum_second_cycle_evidence_object_outcome": str(
                    minimum_evidence_summary.get("terminal_outcome", "")
                ).strip(),
                "material_repeatability_admissibility_criteria_outcome": str(
                    material_repeatability_criteria_summary.get("terminal_outcome", "")
                ).strip(),
                "approval_eligible_policy_review_outcome": str(
                    approval_eligible_review_outcome_summary.get("terminal_outcome", "")
                ).strip(),
                "no_further_external_validation_path_triggered": no_further_external_validation_path_triggered,
            },
            "summary": {
                "all_criteria_satisfied": review_outcome
                in {
                    "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
                    "ADMISSIBLE_CROSS_PROBE_STANDARD_DEFINED",
                    "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "admissibility_outcome": admissibility_outcome,
            "naming_outcome": naming_outcome,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_admissibility_standard_review_report": _ptr(admissibility_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_path),
            "bridge_minimum_second_cycle_evidence_object_report": _ptr(minimum_evidence_path),
            "bridge_material_repeatability_admissibility_criteria_report": _ptr(material_repeatability_criteria_path),
            "bridge_approval_eligible_policy_review_outcome_report": _ptr(approval_eligible_review_outcome_path),
        },
        "non_claim_boundary": "Repository-local bridge external-validation policy review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the bridge external-validation policy review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "bridge_external_validation_policy_review_20260412_v0.json",
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
        "bridge_external_validation_policy_review_report: "
        f"review_outcome={payload['summary']['review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
