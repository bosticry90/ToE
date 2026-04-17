from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_20260414_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("approval_eligible_policy_review_outcome_policy", {}))
    contract = dict(declaration.get("approval_eligible_policy_review_outcome_contract", {}))

    named_check_path = REPO_ROOT / str(
        required_inputs.get("bridge_first_named_repeatability_check_report", "")
    ).strip()
    minimum_evidence_path = REPO_ROOT / str(
        required_inputs.get("bridge_minimum_second_cycle_evidence_object_report", "")
    ).strip()
    material_criteria_path = REPO_ROOT / str(
        required_inputs.get("bridge_material_repeatability_admissibility_criteria_report", "")
    ).strip()
    approval_criteria_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_criteria_report", "")
    ).strip()
    note_path = REPO_ROOT / str(
        required_inputs.get("approval_eligible_policy_review_outcome_note", "")
    ).strip()

    named_check = _read_json(named_check_path)
    minimum_evidence = _read_json(minimum_evidence_path)
    material_criteria = _read_json(material_criteria_path)
    approval_criteria = _read_json(approval_criteria_path)
    note_text = _read_text(note_path)

    named_check_summary = dict(named_check.get("summary", {}))
    minimum_evidence_summary = dict(minimum_evidence.get("summary", {}))
    material_criteria_summary = dict(material_criteria.get("summary", {}))
    approval_criteria_summary = dict(approval_criteria.get("summary", {}))

    named_check_outcome = str(named_check_summary.get("terminal_outcome", "")).strip()
    minimum_evidence_outcome = str(minimum_evidence_summary.get("terminal_outcome", "")).strip()
    material_criteria_outcome = str(material_criteria_summary.get("terminal_outcome", "")).strip()
    approval_criteria_outcome = str(approval_criteria_summary.get("terminal_outcome", "")).strip()

    required_named_check_outcome = str(policy.get("required_named_repeatability_check_outcome", "")).strip()
    required_minimum_evidence_outcome = str(
        policy.get("required_minimum_second_cycle_evidence_object_outcome", "")
    ).strip()
    required_material_criteria_outcome = str(
        policy.get("required_material_repeatability_admissibility_criteria_outcome", "")
    ).strip()
    required_approval_criteria_outcome = str(
        policy.get("required_policy_standard_approval_criteria_outcome", "")
    ).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))

    named_check_admissible = bool(named_check_summary.get("named_check_admissible", False))
    minimum_evidence_defined = bool(
        minimum_evidence_summary.get("second_cycle_minimum_evidence_defined", False)
    )
    material_criteria_defined = bool(
        material_criteria_summary.get("repeatability_admissibility_criteria_defined", False)
    )
    approval_criteria_defined = bool(
        approval_criteria_summary.get("policy_standard_approval_criteria_defined", False)
    )
    approval_attestation_surfaces_declared = bool(
        approval_criteria_summary.get("approval_attestation_surfaces_declared", False)
    )
    approval_minimum_evidence_requirement_defined = bool(
        approval_criteria_summary.get("approval_minimum_evidence_requirement_defined", False)
    )
    policy_standard_approval_recorded = bool(
        approval_criteria_summary.get("policy_standard_approval_recorded", False)
    )

    approval_eligible_repeatability_review_outcome_defined = bool(
        policy.get("approval_eligible_repeatability_review_outcome_defined", False)
    )
    require_named_bounded_repeatability_check_only = bool(
        policy.get("require_named_bounded_repeatability_check_only", False)
    )
    require_material_repeatability_admissibility_criteria_defined = bool(
        policy.get("require_material_repeatability_admissibility_criteria_defined", False)
    )
    require_minimum_second_cycle_evidence_object_declared = bool(
        policy.get("require_minimum_second_cycle_evidence_object_declared", False)
    )
    require_policy_standard_approval_criteria_defined = bool(
        policy.get("require_policy_standard_approval_criteria_defined", False)
    )
    require_approval_record_distinct_from_review_eligibility = bool(
        policy.get("require_approval_record_distinct_from_review_eligibility", False)
    )

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    policy_shape_ok = all(
        key in policy
        for key in [
            "required_named_repeatability_check_outcome",
            "required_minimum_second_cycle_evidence_object_outcome",
            "required_material_repeatability_admissibility_criteria_outcome",
            "required_policy_standard_approval_criteria_outcome",
            "required_note_tokens",
            "approval_eligible_repeatability_review_outcome_defined",
            "require_named_bounded_repeatability_check_only",
            "require_material_repeatability_admissibility_criteria_defined",
            "require_minimum_second_cycle_evidence_object_declared",
            "require_policy_standard_approval_criteria_defined",
            "require_approval_record_distinct_from_review_eligibility",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        named_check_outcome == required_named_check_outcome
        and minimum_evidence_outcome == required_minimum_evidence_outcome
        and material_criteria_outcome == required_material_criteria_outcome
        and approval_criteria_outcome == required_approval_criteria_outcome
        and named_check_admissible
        and minimum_evidence_defined
        and material_criteria_defined
        and approval_criteria_defined
        and approval_attestation_surfaces_declared
        and approval_minimum_evidence_requirement_defined
        and not policy_standard_approval_recorded
        and note_tokens_present
        and approval_eligible_repeatability_review_outcome_defined
        and require_named_bounded_repeatability_check_only
        and require_material_repeatability_admissibility_criteria_defined
        and require_minimum_second_cycle_evidence_object_declared
        and require_policy_standard_approval_criteria_defined
        and require_approval_record_distinct_from_review_eligibility
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_DECLARED"
        next_action = "ALLOW_POLICY_REVIEW_TO_EMIT_AN_APPROVAL_ELIGIBLE_REPEATABILITY_OUTCOME_WITHOUT_RECORDING_APPROVAL"
    else:
        terminal_outcome = "RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "named_repeatability_check_outcome_match": named_check_outcome == required_named_check_outcome,
            "minimum_second_cycle_evidence_object_outcome_match": minimum_evidence_outcome
            == required_minimum_evidence_outcome,
            "material_repeatability_admissibility_criteria_outcome_match": material_criteria_outcome
            == required_material_criteria_outcome,
            "policy_standard_approval_criteria_outcome_match": approval_criteria_outcome
            == required_approval_criteria_outcome,
            "named_check_admissible": named_check_admissible,
            "minimum_second_cycle_evidence_defined": minimum_evidence_defined,
            "material_repeatability_admissibility_criteria_defined": material_criteria_defined,
            "policy_standard_approval_criteria_defined": approval_criteria_defined,
            "approval_attestation_surfaces_declared": approval_attestation_surfaces_declared,
            "approval_minimum_evidence_requirement_defined": approval_minimum_evidence_requirement_defined,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "note_tokens_present": note_tokens_present,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_APPROVAL_ELIGIBLE_POLICY_REVIEW_OUTCOME_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "approval_eligible_review_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "named_check_outcome": named_check_outcome,
                "minimum_evidence_outcome": minimum_evidence_outcome,
                "material_repeatability_admissibility_criteria_outcome": material_criteria_outcome,
                "policy_standard_approval_criteria_outcome": approval_criteria_outcome,
                "named_check_admissible": named_check_admissible,
                "minimum_second_cycle_evidence_defined": minimum_evidence_defined,
                "minimum_second_cycle_evidence_satisfied": bool(
                    minimum_evidence_summary.get("second_cycle_minimum_evidence_satisfied", False)
                ),
                "material_repeatability_admissibility_criteria_defined": material_criteria_defined,
                "policy_standard_approval_criteria_defined": approval_criteria_defined,
                "approval_attestation_surfaces_declared": approval_attestation_surfaces_declared,
                "approval_minimum_evidence_requirement_defined": approval_minimum_evidence_requirement_defined,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
                "approval_eligible_repeatability_review_outcome_defined": approval_eligible_repeatability_review_outcome_defined,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "approval_eligible_repeatability_review_outcome_defined": approval_eligible_repeatability_review_outcome_defined,
            "named_check_admissible": named_check_admissible,
            "minimum_second_cycle_evidence_defined": minimum_evidence_defined,
            "minimum_second_cycle_evidence_satisfied": bool(
                minimum_evidence_summary.get("second_cycle_minimum_evidence_satisfied", False)
            ),
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_first_named_repeatability_check_report": _ptr(named_check_path),
            "bridge_minimum_second_cycle_evidence_object_report": _ptr(minimum_evidence_path),
            "bridge_material_repeatability_admissibility_criteria_report": _ptr(material_criteria_path),
            "bridge_policy_standard_approval_criteria_report": _ptr(approval_criteria_path),
            "approval_eligible_policy_review_outcome_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge approval-eligible policy-review outcome report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the RL10 bridge approval-eligible policy-review outcome report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_approval_eligible_policy_review_outcome_20260414_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_approval_eligible_policy_review_outcome_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())