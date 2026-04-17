from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_REPORT_20260413_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_20260413_v0.json"
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
    contract = dict(declaration.get("policy_standard_contract", {}))
    outcome_contract = dict(declaration.get("policy_standard_outcome_contract", {}))

    review_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()
    admissibility_path = REPO_ROOT / str(
        required_inputs.get("bridge_admissibility_standard_review_report", "")
    ).strip()
    naming_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()
    bounded_check_family_path = REPO_ROOT / str(
        required_inputs.get("bridge_bounded_check_family_standard_report", "")
    ).strip()
    approval_criteria_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_criteria_report", "")
    ).strip()
    approval_record_surface_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_record_surface_report", "")
    ).strip()
    approval_record_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_record_report", "")
    ).strip()

    review = _read_json(review_path)
    admissibility = _read_json(admissibility_path)
    naming = _read_json(naming_path)
    bounded_check_family = _read_json(bounded_check_family_path)
    approval_criteria = _read_json(approval_criteria_path)
    approval_record_surface = _read_json(approval_record_surface_path)
    approval_record = _read_json(approval_record_path)

    review_summary = dict(review.get("summary", {}))
    review_inputs = dict(dict(review.get("objective_quality", {})).get("inputs", {}))
    admissibility_summary = dict(admissibility.get("summary", {}))
    admissibility_inputs = dict(dict(admissibility.get("objective_quality", {})).get("inputs", {}))
    naming_summary = dict(naming.get("summary", {}))
    naming_inputs = dict(dict(naming.get("objective_quality", {})).get("inputs", {}))
    naming_criteria = dict(naming.get("criteria", {}))
    bounded_check_family_summary = dict(bounded_check_family.get("summary", {}))
    approval_criteria_summary = dict(approval_criteria.get("summary", {}))
    approval_record_surface_summary = dict(approval_record_surface.get("summary", {}))
    approval_record_summary = dict(approval_record.get("summary", {}))

    review_outcome = str(review_summary.get("review_outcome", "")).strip()
    admissibility_outcome = str(admissibility_summary.get("review_outcome", "")).strip()
    naming_outcome = str(naming_summary.get("review_outcome", "")).strip()

    declaration_standard_defined = bool(
        admissibility_inputs.get("declaration_standard_defined", False)
        or bounded_check_family_summary.get("declaration_standard_defined", False)
    )
    bounded_check_families_defined = bool(
        admissibility_inputs.get("bounded_check_families_defined", False)
        or bounded_check_family_summary.get("bounded_check_families_defined", False)
    )
    external_validation_policy_surface_defined = bool(
        admissibility_inputs.get("external_validation_policy_surface_defined", False)
        or bounded_check_family_summary.get("external_validation_policy_surface_defined", False)
    )
    named_check_admissible = bool(
        naming_inputs.get(
            "named_check_admissible",
            naming_summary.get("named_check_admissible", naming_criteria.get("named_check_admissible", False)),
        )
    )
    bounded_scope_declared = bool(naming_inputs.get("bounded_scope_declared", False))
    not_disguised_second_full_cycle_declared = bool(
        naming_inputs.get("not_disguised_second_full_cycle_declared", False)
    )
    second_cycle_minimum_evidence_defined = bool(
        review_inputs.get("second_cycle_minimum_evidence_defined", False)
    )
    repeatability_admissibility_criteria_defined = bool(
        review_inputs.get("repeatability_admissibility_criteria_defined", False)
    )
    cross_probe_admissibility_criteria_defined = bool(
        review_inputs.get("cross_probe_admissibility_criteria_defined", False)
    )
    policy_approval_criteria_defined = bool(
        approval_criteria_summary.get("policy_standard_approval_criteria_defined", False)
    )
    approval_attestation_surfaces_declared = bool(
        approval_criteria_summary.get("approval_attestation_surfaces_declared", False)
    )
    approval_minimum_evidence_requirement_defined = bool(
        approval_criteria_summary.get("approval_minimum_evidence_requirement_defined", False)
    )
    policy_standard_approval_record_surface_defined = bool(
        approval_record_surface_summary.get("policy_standard_approval_record_surface_defined", False)
    )
    policy_standard_approval_record_defined = bool(
        approval_record_summary.get("policy_standard_approval_record_defined", False)
    )
    policy_standard_approval_recorded = bool(
        approval_record_summary.get("policy_standard_approval_recorded", False)
    )

    required_review_outcome = str(contract.get("required_review_outcome", "")).strip()
    allowed_review_outcomes_for_approval = set(contract.get("allowed_review_outcomes_for_approval", []))
    allowed_naming_outcomes_for_standard = set(contract.get("allowed_naming_outcomes_for_standard", []))
    require_declaration_standard_defined = bool(contract.get("require_declaration_standard_defined", False))
    require_bounded_check_families_defined = bool(contract.get("require_bounded_check_families_defined", False))
    require_external_validation_policy_surface = bool(
        contract.get("require_external_validation_policy_surface", False)
    )
    require_one_admissible_bounded_check_named = bool(
        contract.get("require_one_admissible_bounded_check_named", False)
    )
    require_second_cycle_minimum_evidence_defined = bool(
        contract.get("require_second_cycle_minimum_evidence_defined", False)
    )
    require_policy_approval_criteria_defined_for_approval = bool(
        contract.get("require_policy_approval_criteria_defined_for_approval", False)
    )
    require_approval_attestation_surfaces_declared_for_approval = bool(
        contract.get("require_approval_attestation_surfaces_declared_for_approval", False)
    )
    require_approval_minimum_evidence_requirement_defined_for_approval = bool(
        contract.get("require_approval_minimum_evidence_requirement_defined_for_approval", False)
    )
    require_policy_standard_approval_record_surface_defined_for_approval = bool(
        contract.get("require_policy_standard_approval_record_surface_defined_for_approval", False)
    )
    require_policy_standard_approval_record_defined_for_approval = bool(
        contract.get("require_policy_standard_approval_record_defined_for_approval", False)
    )
    require_policy_standard_approval_record_for_approval = bool(
        contract.get("require_policy_standard_approval_record_for_approval", False)
    )

    contract_shape_ok = all(
        key in contract
        for key in [
            "required_review_outcome",
            "allowed_review_outcomes_for_approval",
            "allowed_naming_outcomes_for_standard",
            "require_declaration_standard_defined",
            "require_bounded_check_families_defined",
            "require_external_validation_policy_surface",
            "require_one_admissible_bounded_check_named",
            "require_second_cycle_minimum_evidence_defined",
            "require_policy_approval_criteria_defined_for_approval",
            "require_approval_attestation_surfaces_declared_for_approval",
            "require_approval_minimum_evidence_requirement_defined_for_approval",
            "require_policy_standard_approval_record_surface_defined_for_approval",
            "require_policy_standard_approval_record_defined_for_approval",
            "require_policy_standard_approval_record_for_approval",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    standard_defined = (
        (declaration_standard_defined or not require_declaration_standard_defined)
        and (bounded_check_families_defined or not require_bounded_check_families_defined)
        and (external_validation_policy_surface_defined or not require_external_validation_policy_surface)
        and (named_check_admissible or not require_one_admissible_bounded_check_named)
        and (naming_outcome in allowed_naming_outcomes_for_standard or not require_one_admissible_bounded_check_named)
        and bounded_scope_declared
        and not_disguised_second_full_cycle_declared
        and (second_cycle_minimum_evidence_defined or not require_second_cycle_minimum_evidence_defined)
    )
    policy_standard_approved = (
        review_outcome in allowed_review_outcomes_for_approval
        and standard_defined
        and (repeatability_admissibility_criteria_defined or cross_probe_admissibility_criteria_defined)
        and (
            policy_approval_criteria_defined
            or not require_policy_approval_criteria_defined_for_approval
        )
        and (
            approval_attestation_surfaces_declared
            or not require_approval_attestation_surfaces_declared_for_approval
        )
        and (
            approval_minimum_evidence_requirement_defined
            or not require_approval_minimum_evidence_requirement_defined_for_approval
        )
        and (
            policy_standard_approval_record_surface_defined
            or not require_policy_standard_approval_record_surface_defined_for_approval
        )
        and (
            policy_standard_approval_record_defined
            or not require_policy_standard_approval_record_defined_for_approval
        )
        and (
            policy_standard_approval_recorded
            or not require_policy_standard_approval_record_for_approval
        )
    )

    defined_criteria_satisfied: list[str] = []
    if declaration_standard_defined:
        defined_criteria_satisfied.append("declaration_standard_defined")
    if bounded_check_families_defined:
        defined_criteria_satisfied.append("bounded_check_families_defined")
    if external_validation_policy_surface_defined:
        defined_criteria_satisfied.append("external_validation_policy_surface_defined")
    if named_check_admissible:
        defined_criteria_satisfied.append("named_check_admissible")
    if naming_outcome in allowed_naming_outcomes_for_standard:
        defined_criteria_satisfied.append("bounded_check_named")
    if bounded_scope_declared:
        defined_criteria_satisfied.append("bounded_scope_declared")
    if not_disguised_second_full_cycle_declared:
        defined_criteria_satisfied.append("not_disguised_second_full_cycle_declared")
    if second_cycle_minimum_evidence_defined:
        defined_criteria_satisfied.append("second_cycle_minimum_evidence_defined")

    approval_criteria_missing: list[str] = []
    if review_outcome not in allowed_review_outcomes_for_approval:
        approval_criteria_missing.append("approval_eligible_policy_review_outcome_missing")
    if not (repeatability_admissibility_criteria_defined or cross_probe_admissibility_criteria_defined):
        approval_criteria_missing.append("material_admissibility_criteria_definition_missing")
    if require_policy_approval_criteria_defined_for_approval and not policy_approval_criteria_defined:
        approval_criteria_missing.append("policy_approval_criteria_not_declared")
    if require_approval_attestation_surfaces_declared_for_approval and not approval_attestation_surfaces_declared:
        approval_criteria_missing.append("approval_attestation_surfaces_not_declared")
    if (
        require_approval_minimum_evidence_requirement_defined_for_approval
        and not approval_minimum_evidence_requirement_defined
    ):
        approval_criteria_missing.append("approval_minimum_evidence_requirement_not_declared")
    if (
        require_policy_standard_approval_record_surface_defined_for_approval
        and not policy_standard_approval_record_surface_defined
    ):
        approval_criteria_missing.append("policy_standard_approval_record_surface_not_declared")
    if (
        require_policy_standard_approval_record_defined_for_approval
        and not policy_standard_approval_record_defined
    ):
        approval_criteria_missing.append("policy_standard_approval_record_not_declared")
    if require_policy_standard_approval_record_for_approval and not policy_standard_approval_recorded:
        approval_criteria_missing.append("policy_standard_approval_not_recorded")

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "EXTERNAL_VALIDATION_POLICY_STANDARD_INCOMPLETE_HOLD")
    ).strip()

    if not contract_shape_ok:
        terminal_outcome = "HOLD_PENDING_EXTERNAL_VALIDATION_POLICY_STANDARD_REPAIR"
        next_action = "REPAIR_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_SHAPE"
    elif policy_standard_approved:
        terminal_outcome = "EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVED_AND_TRIGGER_AUTHORIZED"
        next_action = "SURFACE_APPROVED_POLICY_STANDARD_TO_HIGHER_LEVEL_POLICY_RESTART_TRIGGER"
    elif standard_defined:
        terminal_outcome = "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED"
        next_action = "APPROVE_OR_ROUTE_DEFINED_POLICY_STANDARD_BEFORE_TRIGGER_AUTHORIZATION"
    else:
        terminal_outcome = "EXTERNAL_VALIDATION_POLICY_STANDARD_INCOMPLETE_HOLD"
        next_action = "DEFINE_DECLARATION_STANDARD_BOUNDED_CHECK_AND_MINIMUM_EVIDENCE_BEFORE_TRIGGER_AUTHORIZATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "review_outcome_is_current_hold": review_outcome == required_review_outcome,
            "declaration_standard_defined": declaration_standard_defined,
            "bounded_check_families_defined": bounded_check_families_defined,
            "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
            "named_check_admissible": named_check_admissible,
            "bounded_scope_declared": bounded_scope_declared,
            "not_disguised_second_full_cycle_declared": not_disguised_second_full_cycle_declared,
            "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
            "policy_approval_criteria_defined": policy_approval_criteria_defined,
            "approval_attestation_surfaces_declared": approval_attestation_surfaces_declared,
            "approval_minimum_evidence_requirement_defined": approval_minimum_evidence_requirement_defined,
            "policy_standard_approval_record_surface_defined": policy_standard_approval_record_surface_defined,
            "policy_standard_approval_record_defined": policy_standard_approval_record_defined,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "policy_standard_defined": standard_defined,
            "policy_standard_approved": policy_standard_approved,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALIZATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "policy_standard_contract_shape_ok": contract_shape_ok,
            },
            "inputs": {
                "review_outcome": review_outcome,
                "required_review_outcome": required_review_outcome,
                "admissibility_outcome": admissibility_outcome,
                "naming_outcome": naming_outcome,
                "declaration_standard_defined": declaration_standard_defined,
                "bounded_check_families_defined": bounded_check_families_defined,
                "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
                "named_check_admissible": named_check_admissible,
                "bounded_scope_declared": bounded_scope_declared,
                "not_disguised_second_full_cycle_declared": not_disguised_second_full_cycle_declared,
                "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
                "repeatability_admissibility_criteria_defined": repeatability_admissibility_criteria_defined,
                "cross_probe_admissibility_criteria_defined": cross_probe_admissibility_criteria_defined,
                "policy_approval_criteria_defined": policy_approval_criteria_defined,
                "approval_attestation_surfaces_declared": approval_attestation_surfaces_declared,
                "approval_minimum_evidence_requirement_defined": approval_minimum_evidence_requirement_defined,
                "policy_standard_approval_record_surface_defined": policy_standard_approval_record_surface_defined,
                "policy_standard_approval_record_defined": policy_standard_approval_record_defined,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
                "bounded_check_family_standard_outcome": str(
                    bounded_check_family_summary.get("terminal_outcome", "")
                ).strip(),
                "policy_standard_approval_criteria_outcome": str(
                    approval_criteria_summary.get("terminal_outcome", "")
                ).strip(),
                "policy_standard_approval_record_surface_outcome": str(
                    approval_record_surface_summary.get("terminal_outcome", "")
                ).strip(),
                "policy_standard_approval_record_outcome": str(
                    approval_record_summary.get("terminal_outcome", "")
                ).strip(),
                "policy_standard_defined": standard_defined,
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
            "policy_standard_defined": standard_defined,
            "policy_standard_approved": policy_standard_approved,
            "review_outcome": review_outcome,
            "admissibility_outcome": admissibility_outcome,
            "naming_outcome": naming_outcome,
            "next_action": next_action,
            "defined_criteria_satisfied": defined_criteria_satisfied,
            "approval_criteria_missing": approval_criteria_missing,
            "remaining_blockers_to_authorization": approval_criteria_missing,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_external_validation_policy_review_report": _ptr(review_path),
            "bridge_admissibility_standard_review_report": _ptr(admissibility_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_path),
            "bridge_bounded_check_family_standard_report": _ptr(bounded_check_family_path),
            "bridge_policy_standard_approval_criteria_report": _ptr(approval_criteria_path),
            "bridge_policy_standard_approval_record_surface_report": _ptr(approval_record_surface_path),
            "bridge_policy_standard_approval_record_report": _ptr(approval_record_path),
        },
        "non_claim_boundary": "Repository-local external-validation policy standard formalization report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate external-validation policy standard formalization report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "bridge_external_validation_policy_standard_formalization_20260413_v0.json",
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
        "bridge_external_validation_policy_standard_formalization_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())