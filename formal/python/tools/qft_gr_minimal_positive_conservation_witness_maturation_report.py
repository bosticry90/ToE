from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_20260614_v0"
PACKET_ID = "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_PACKET_PREPARED_"
    "WITH_STRICT_TOY_SCOPE_AND_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_maturation_packet_prepared_"
    "with_strict_toy_scope_no_source_admissibility_or_qft_gr_closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_positive_conservation_witness_maturation_packet_result"
NEXT_TARGET_KIND = "qft_gr_minimal_positive_conservation_witness_maturation_packet_result_review"
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction"
)
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source"
)
MATURED_WITNESS_ATTEMPT_TARGET = (
    "execute_qft_gr_minimal_positive_conservation_witness_maturation_attempt"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_20260614_v0.json"
)
DEFAULT_MARKDOWN_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_REPORT_v0.md"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalPositiveConservationWitnessMaturation.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _witness_proves() -> list[dict[str, str]]:
    return [
        {
            "claim_id": "strict_toy_local_weak_conservation_bridge_witness",
            "status": "accepted_local_witness_only",
            "statement": (
                "Under strict toy assumptions, residual zero plus a supplied "
                "divergence identity plus allowed weak pairing plus compact-"
                "support/no-boundary assumptions imply weak conservation "
                "against allowed tests."
            ),
            "scope": "strict_toy_allowed_tests_only",
        },
        {
            "claim_id": "theorem_shape_confirmed",
            "status": "theorem_bearing_attempt_result_reviewed",
            "statement": (
                "The accepted Lean bridge is theorem-shaped and reuses the "
                "strict toy conservation theorem from the witness attempt."
            ),
            "scope": "local_formal_bridge_template",
        },
    ]


def _strict_toy_assumptions() -> list[dict[str, str]]:
    return [
        {
            "assumption_id": "strict_toy_compact_support_smooth_test_vector_class_v0",
            "role": "allowed weak test class",
            "maturation_status": "fixed_for_local_witness_not_full_test_universe",
        },
        {
            "assumption_id": "strict_toy_source_test_pairing_v0",
            "role": "weak pairing",
            "maturation_status": "available_for_local_witness_domain_not_expanded",
        },
        {
            "assumption_id": "strict_toy_stress_energy_like_source_object_v0",
            "role": "source object",
            "maturation_status": "stress_energy_like_only_not_source_admissible",
        },
        {
            "assumption_id": "strict_toy_weak_divergence_pairing_v0",
            "role": "weak divergence pairing",
            "maturation_status": "local_pairing_only_not_broad_covariant_conservation",
        },
        {
            "assumption_id": "strict_toy_field_equation_residual_zero_v0",
            "role": "field-equation residual antecedent",
            "maturation_status": "supplied_zero_residual_not_yet_derived_from_real_field_equation",
        },
        {
            "assumption_id": "strict_toy_divergence_identity_assumption_v0",
            "role": "divergence identity antecedent",
            "maturation_status": "supplied_identity_not_yet_derived",
        },
        {
            "assumption_id": "strict_toy_compact_support_no_boundary_condition_v0",
            "role": "boundary-term removal",
            "maturation_status": "compact_support_no_boundary_only_not_general_boundary_control",
        },
    ]


def _supplied_not_derived() -> list[dict[str, str]]:
    return [
        {
            "item": "divergence_identity",
            "status": "supplied_not_derived",
            "required_maturation": (
                "Derive the divergence identity from a specified source object "
                "and field equation, or isolate the exact additional axiom."
            ),
        },
        {
            "item": "residual_zero_to_real_field_equation_link",
            "status": "supplied_not_derived",
            "required_maturation": (
                "Connect residual zero to an explicit field equation rather "
                "than treating it as a free antecedent."
            ),
        },
        {
            "item": "allowed_weak_pairing_domain",
            "status": "fixed_local_domain_only",
            "required_maturation": (
                "Expand or justify the weak pairing domain and prove that the "
                "pairing supports the required weak-divergence operation."
            ),
        },
        {
            "item": "compact_support_no_boundary_condition",
            "status": "local_boundary_simplification",
            "required_maturation": (
                "Replace the no-boundary assumption with controlled boundary "
                "terms or a justified support condition."
            ),
        },
        {
            "item": "source_object_physical_admissibility",
            "status": "not_established",
            "required_maturation": (
                "Show the source object is defined in the right domain with "
                "regularity, pairing, and source-map provenance."
            ),
        },
        {
            "item": "Bianchi_compatibility",
            "status": "not_established",
            "required_maturation": (
                "Show compatibility with the Bianchi identity before any "
                "Einstein-like coupling is considered."
            ),
        },
    ]


def _before_source_admissibility_requirements() -> list[dict[str, str]]:
    return [
        {
            "requirement": "defined_source_object",
            "status": "not_yet_satisfied_beyond_strict_toy_source_object",
        },
        {
            "requirement": "weak_conservation_beyond_strict_toy_tests",
            "status": "not_yet_satisfied",
        },
        {
            "requirement": "regularity_and_derivative_exchange_support",
            "status": "not_yet_satisfied",
        },
        {
            "requirement": "weak_pairing_domain_without_unresolved_obstruction",
            "status": "not_yet_satisfied",
        },
        {
            "requirement": "Bianchi_compatibility_condition",
            "status": "not_yet_satisfied",
        },
        {
            "requirement": "semiclassical_source_map_provenance",
            "status": "not_yet_satisfied",
        },
        {
            "requirement": "known_limit_compatibility",
            "status": "not_yet_satisfied",
        },
    ]


def _maturation_questions() -> list[dict[str, str]]:
    return [
        {
            "question": "Can the supplied divergence identity be derived?",
            "target_kind": "derivation_or_explicit_axiom_ledger_entry",
        },
        {
            "question": "Can residual zero be tied to a concrete field equation?",
            "target_kind": "field_equation_link_packet_or_attempt",
        },
        {
            "question": "Can the allowed weak pairing domain be widened safely?",
            "target_kind": "weak_pairing_domain_maturation_or_countermodel",
        },
        {
            "question": "Can compact support/no-boundary assumptions be relaxed?",
            "target_kind": "boundary_term_control_packet",
        },
        {
            "question": "What source-map ladder is needed before admissibility?",
            "target_kind": "source_map_ladder_follow_on",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "This checkpoint prepares only the maturation packet, so the "
                "next action is bounded packet result review."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The packet-preparation target is consumed by this packet.",
        },
        {
            "target": MATURED_WITNESS_ATTEMPT_TARGET,
            "decision": "not_authorized_until_packet_review",
            "reason": "No maturation attempt is authorized by packet preparation alone.",
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on_not_selected",
            "reason": "Countermodel work remains a later route if maturation fails.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected",
            "reason": "Source-map ladder work remains downstream of maturation review.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The maturation packet explicitly says admissibility remains forbidden.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility is a future requirement, not a packet result.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "No semiclassical Einstein equation is derived.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "The local strict toy witness does not close QFT-GR.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
        {
            "target": "promote_master_action",
            "decision": "not_authorized",
            "reason": "The master action is not promoted.",
        },
    ]


def _validation_policy(result_review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_positive_conservation_witness_maturation_packet_preparation",
        "routine_packet_uses_bounded_target_relevant_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "long_running_validation_escalation_authorized": False,
        "timeout_rerun_loop_authorized": False,
        "timeout_recorded_as_caveat_not_rerun_instruction": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "inherited_result_review_validation_policy": result_review.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_positive_conservation_witness_maturation_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(result_review)
    witness_proves = _witness_proves()
    strict_toy_assumptions = _strict_toy_assumptions()
    supplied_not_derived = _supplied_not_derived()
    source_admissibility_requirements = _before_source_admissibility_requirements()

    acceptance_criteria = {
        "consumes_expected_result_review": (
            result_review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and result_review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and result_review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and result_review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "accepted_local_witness_carried": (
            result_review.get("strict_toy_witness_accepted") is True
            and result_review.get("local_conservation_bridge_witness_accepted") is True
            and result_review.get("strict_toy_weak_conservation_witness_achieved")
            is True
            and result_review.get("weak_conservation_against_allowed_tests_proved")
            is True
        ),
        "packet_explains_witness_and_assumptions": (
            len(witness_proves) == 2
            and len(strict_toy_assumptions) == 7
            and len(supplied_not_derived) == 6
            and len(source_admissibility_requirements) == 7
        ),
        "supplied_not_derived_items_are_explicit": {
            row["item"] for row in supplied_not_derived
        }
        == {
            "divergence_identity",
            "residual_zero_to_real_field_equation_link",
            "allowed_weak_pairing_domain",
            "compact_support_no_boundary_condition",
            "source_object_physical_admissibility",
            "Bianchi_compatibility",
        },
        "source_admissibility_preconditions_not_satisfied": all(
            row["status"].startswith("not_yet_satisfied")
            for row in source_admissibility_requirements
        ),
        "selects_result_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "no_source_admissibility_or_qft_gr_closure": (
            result_review.get("source_admissibility_claimed") is False
            and result_review.get("Bianchi_compatibility_claimed") is False
            and result_review.get("semiclassical_einstein_equation_derived") is False
            and result_review.get("qft_gr_seam_closed") is False
            and result_review.get("qft_gr_source_map_closure_claimed") is False
        ),
        "no_broad_conservation_claim": (
            result_review.get("conservation_claimed") is False
            and result_review.get("conservation_proved") is False
            and result_review.get("conservation_proof_object_constructed") is False
            and result_review.get("conservation_witness_constructed") is False
            and result_review.get("full_qft_gr_conservation_claimed") is False
            and result_review.get("unbounded_conservation_proved") is False
        ),
        "no_empirical_public_or_master_action_promotion": (
            result_review.get("empirical_validation_claimed") is False
            and result_review.get("public_submission_authorized") is False
            and result_review.get("master_action_promoted") is False
            and result_review.get("master_action_promotion_authorized") is False
        ),
        "routine_validation_policy_preserves_non_escalation": all(
            validation_policy[key] is False
            for key in [
                "full_pytest_required",
                "full_governance_suite_required",
                "full_aggregate_lean_required",
                "full_ci_parity_required",
                "full_security_scan_required",
                "long_running_validation_escalation_authorized",
                "timeout_rerun_loop_authorized",
                "aggregate_lean_health_claimed",
            ]
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_PACKET"
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "packet_prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_positive_conservation_witness_maturation_packet_requires_remediation",
        "consumed_target": CONSUMED_TARGET,
        "consumes_result_review_id": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "strict_toy_witness_accepted": result_review.get("strict_toy_witness_accepted"),
        "local_conservation_bridge_witness_accepted": result_review.get(
            "local_conservation_bridge_witness_accepted"
        ),
        "local_conservation_bridge_witness_constructed": result_review.get(
            "local_conservation_bridge_witness_constructed"
        ),
        "strict_toy_weak_conservation_witness_achieved": result_review.get(
            "strict_toy_weak_conservation_witness_achieved"
        ),
        "strict_toy_weak_conservation_theorem_constructed": result_review.get(
            "strict_toy_weak_conservation_theorem_constructed"
        ),
        "weak_conservation_against_allowed_tests_proved": result_review.get(
            "weak_conservation_against_allowed_tests_proved"
        ),
        "strict_toy_assumptions_only": True,
        "local_witness_scope": "strict_toy_local_weak_conservation_bridge_witness_only",
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "theorem_shape": result_review.get("theorem_shape"),
        "proof_strategy": result_review.get("proof_strategy"),
        "witness_proves": witness_proves,
        "strict_toy_assumptions": strict_toy_assumptions,
        "strict_toy_assumption_count": len(strict_toy_assumptions),
        "supplied_not_derived": supplied_not_derived,
        "supplied_not_derived_count": len(supplied_not_derived),
        "maturation_questions": _maturation_questions(),
        "source_admissibility_preconditions_before_consideration": (
            source_admissibility_requirements
        ),
        "source_admissibility_precondition_count": len(
            source_admissibility_requirements
        ),
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": "stabilized_for_next_target_selection_not_resolved",
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "maturation_packet_prepared": accepted,
        "maturation_attempt_authorized": False,
        "maturation_packet_result_reviewed": False,
        "countermodel_lane_retained_as_follow_on": True,
        "countermodel_packet_authorized": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "source_admissibility_can_be_considered": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "full_qft_gr_conservation_claimed": False,
        "unbounded_conservation_proved": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_packet_current_target_registry_gate": "required_for_checkpoint",
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "targeted_lean_packet_frontier_import_checks": "required_for_checkpoint",
            "git_diff_check": "required_for_checkpoint",
            "full_pytest": "not_required_for_checkpoint",
            "full_governance_suite": "not_required_for_checkpoint",
            "full_aggregate_lean": "not_required_for_checkpoint_preserved_caveat",
            "release_index_lean_path": "not_freshly_validated_preserved_caveat",
            "full_ci_parity": "not_required_for_checkpoint",
            "security_scan": "not_required_for_checkpoint",
        },
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded maturation-packet checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "markdown_report": _ptr(DEFAULT_MARKDOWN_OUT),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "acceptance_criteria": acceptance_criteria,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_"
            "PACKET_RESULT_ONLY_NO_MATURATION_ATTEMPT_NO_COUNTERMODEL_SELECTION_"
            "NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_"
            "CLOSURE_EMPIRICAL_VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "non_claim_boundary": (
            "This packet matures only the accepted strict toy local weak-"
            "conservation bridge witness by recording what it proves, which "
            "antecedents remain supplied rather than derived, and what must be "
            "discharged before source admissibility can even be considered. It "
            "preserves no broad QFT-GR conservation claim, no source "
            "admissibility, no Bianchi compatibility, no semiclassical "
            "Einstein equation, no QFT-GR closure, no empirical validation, "
            "no public submission, and no master-action promotion."
        ),
    }


def render_markdown(packet: dict[str, Any]) -> str:
    lines = [
        "# QFT-GR Minimal Positive Conservation Witness Maturation Packet v0",
        "",
        f"- Outcome: `{packet['outcome_id']}`",
        f"- Selected next target: `{packet['selected_next_target']}`",
        f"- Local witness scope: `{packet['local_witness_scope']}`",
        "",
        "## What The Witness Proves",
    ]
    for row in packet["witness_proves"]:
        lines.append(f"- `{row['claim_id']}`: {row['statement']}")

    lines.extend(["", "## Strict Toy Assumptions"])
    for row in packet["strict_toy_assumptions"]:
        lines.append(
            f"- `{row['assumption_id']}` ({row['role']}): "
            f"{row['maturation_status']}"
        )

    lines.extend(["", "## Supplied Rather Than Derived"])
    for row in packet["supplied_not_derived"]:
        lines.append(
            f"- `{row['item']}`: {row['status']}; "
            f"{row['required_maturation']}"
        )

    lines.extend(["", "## Before Source Admissibility Can Be Considered"])
    for row in packet["source_admissibility_preconditions_before_consideration"]:
        lines.append(f"- `{row['requirement']}`: {row['status']}")

    lines.extend(["", "## Boundary", packet["non_claim_boundary"], ""])
    return "\n".join(lines)


def write_qft_gr_minimal_positive_conservation_witness_maturation_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    markdown_out: Path = DEFAULT_MARKDOWN_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_positive_conservation_witness_maturation_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_out.parent.mkdir(parents=True, exist_ok=True)
    markdown_out.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR minimal positive conservation witness maturation packet."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--markdown-out", type=Path, default=DEFAULT_MARKDOWN_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    markdown_out = (
        ns.markdown_out
        if ns.markdown_out.is_absolute()
        else (REPO_ROOT / ns.markdown_out)
    )
    payload = write_qft_gr_minimal_positive_conservation_witness_maturation_packet(
        result_review_path=result_review_path,
        out=out,
        markdown_out=markdown_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "markdown_out": _ptr(markdown_out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "packet_prepared": payload["packet_prepared"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
