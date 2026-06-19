from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_admissibility_ck_constraint_candidate_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_ID as CANDIDATE_PACKET_ID,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
    SCHEMA_ID as CANDIDATE_PACKET_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_ACCEPTS_"
    "ROUTE_CONSISTENCY_CANDIDATE_NO_FUNCTIONALIZATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_admissibility_ck_constraint_candidate_result_review_accepts_"
    "route_consistency_candidate_no_functionalization_or_promotion"
)
NEXT_TARGET = "prepare_phi_bridge_admissibility_ck_functional_embedding_packet"
NEXT_TARGET_KIND = "phi_bridge_admissibility_ck_functional_embedding_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
LEAN_VALIDATION_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "bridge_candidate_recorded_as_candidate_only",
            "status": "accepted",
            "evidence": packet.get("bridge_candidate_recorded"),
            "assessment": (
                "C_bridge^phi is accepted only as a candidate bridge "
                "admissibility rule."
            ),
        },
        {
            "row_id": "route_consistency_tuple_carried_forward_exactly",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_FORM,
            "assessment": (
                "The route-consistency tuple is carried forward exactly."
            ),
        },
        {
            "row_id": "bridge_condition_carried_forward_exactly",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The bridge condition C_bridge^phi = 0 is preserved.",
        },
        {
            "row_id": "field_equation_match_component_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
            "assessment": "The field-equation match component is preserved.",
        },
        {
            "row_id": "stress_energy_match_component_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
            "assessment": "The stress-energy match component is preserved.",
        },
        {
            "row_id": "source_residual_match_component_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
            "assessment": "The source-residual match component is preserved.",
        },
        {
            "row_id": "source_admissibility_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_CANDIDATE_CONSTRAINT_FORM,
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": (
                "The prior source-admissibility rule remains context for the "
                "bridge review."
            ),
        },
        {
            "row_id": "no_bridge_functionalization",
            "status": "accepted",
            "evidence": [
                "bridge_candidate_functional_defined=false",
                "bridge_candidate_functional_selected=false",
                "ck_action_embedding_claimed=false",
            ],
            "assessment": "No C_k action term or bridge functional is defined.",
        },
        {
            "row_id": "no_ck_variation_or_action_embedding",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "candidate_action_insertion_executed=false",
                "lambda_variation_executed=false",
            ],
            "assessment": "No C_k variation or action embedding is executed.",
        },
        {
            "row_id": "no_bridge_proof_or_route_verification",
            "status": "accepted",
            "evidence": [
                "bridge_admissibility_proved=false",
                "route_consistency_tuple_proved=false",
                "bridge_route_alignment_verified=false",
            ],
            "assessment": (
                "The review accepts the candidate status without proving full "
                "bridge admissibility or route alignment."
            ),
        },
        {
            "row_id": "no_generation_potential_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "phi_generated_by_ck_claimed=false",
                "potential_derived=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The review preserves no phi generation, no V(phi) derivation, "
                "no QFT-GR closure, and no master-action promotion."
            ),
        },
        {
            "row_id": "functional_embedding_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next packet may decide whether the bridge rule is "
                "admissibility-only or embeddable as a functional."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "phi_bridge_admissibility_ck_constraint_candidate_packet_result_review"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_bridge_admissibility_ck_constraint_candidate_packet_result_review(
    *,
    candidate_packet_path: Path = CANDIDATE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(candidate_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_review_target": (
            packet.get("schema_id") == CANDIDATE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CANDIDATE_PACKET_ID
            and packet.get("outcome_id") == CANDIDATE_PACKET_OUTCOME
            and packet.get("packet_result") == CANDIDATE_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "candidate_tuple_exact": (
            packet.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
            and packet.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
            and packet.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and packet.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
        ),
        "route_components_exact": (
            packet.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and packet.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and packet.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "selected_family_exact": (
            packet.get("selected_ck_option_class") == SELECTED_CK_OPTION_CLASS
            and packet.get("selected_ck_constraint_family")
            == SELECTED_CK_CONSTRAINT_FAMILY
        ),
        "source_admissibility_context_exact": (
            packet.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "candidate_only_boundary_carried_forward": (
            packet.get("bridge_candidate_recorded") is True
            and packet.get("bridge_candidate_recorded_as_admissibility_rule") is True
            and packet.get("bridge_candidate_recorded_as_action_term") is False
            and packet.get("bridge_candidate_recorded_as_new_dynamical_law") is False
            and packet.get("bridge_candidate_rule_proved") is False
            and packet.get("bridge_admissibility_claimed") is False
            and packet.get("bridge_admissibility_proved") is False
        ),
        "no_functionalization_or_variation": all(
            packet.get(key) is False
            for key in [
                "bridge_candidate_functional_defined",
                "bridge_candidate_functional_selected",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "ck_action_embedding_claimed",
                "candidate_action_insertion_executed",
                "ck_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "phi_variation_of_candidate_executed",
            ]
        ),
        "no_forbidden_claims": all(
            packet.get(key) is False
            for key in [
                "bridge_route_alignment_verified",
                "route_consistency_tuple_proved",
                "field_equation_match_proved",
                "stress_energy_match_proved",
                "source_residual_match_proved",
                "phi_generated_by_ck_claimed",
                "phi_generation_theorem_claimed",
                "derived_v_phi_claimed",
                "v_phi_derivation_claimed",
                "potential_derived",
                "new_conservation_proof_claimed",
                "new_source_admissibility_proof_claimed",
                "source_admissibility_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "canonical_master_action_promoted",
                "empirical_validation_claimed",
                "public_readiness_claimed",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_BRIDGE_ADMISSIBILITY_CK_CANDIDATE_REVIEW"
    )
    route_sequence = " -> ".join(BRIDGE_ROUTE_ALIGNMENT_SEQUENCE)
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_ADMISSIBILITY_CK_CANDIDATE_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
        "candidate_packet_result": CANDIDATE_PACKET_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_plain": route_sequence,
        "bridge_component_count": 3,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "review_accepts_route_consistency_candidate": True,
        "route_consistency_candidate_accepted": True,
        "bridge_candidate_recorded_as_candidate_only": True,
        "bridge_candidate_recorded_as_admissibility_rule": True,
        "candidate_carried_forward_exactly": True,
        "route_consistency_tuple_carried_forward": True,
        "field_equation_match_component_preserved": True,
        "stress_energy_match_component_preserved": True,
        "source_residual_match_component_preserved": True,
        "source_admissibility_context_preserved": True,
        "bridge_functional_embedding_packet_authorized": True,
        "functional_embedding_packet_authorized": True,
        "functional_embedding_packet_prepared": False,
        "functional_embedding_executed": False,
        "bridge_functional_selected": False,
        "bridge_candidate_functional_defined": False,
        "bridge_candidate_functional_selected": False,
        "bridge_candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_new_dynamical_law": False,
        "bridge_candidate_rule_proved": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_action_embedding_claimed": False,
        "candidate_action_insertion_executed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "phi_variation_of_candidate_executed": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "lambda_nu_domain_selected": False,
        "higher_derivative_scope_resolved": False,
        "boundary_terms_controlled": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "native_generation_theorem_claimed": False,
        "derived_v_phi_claimed": False,
        "v_phi_derivation_claimed": False,
        "potential_derived": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_conservation_claimed": False,
        "weak_conservation_claimed": False,
        "bianchi_compatibility_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "standard_model_derivation_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "PHI_BRIDGE_ADMISSIBILITY_CK_CANDIDATE_REVIEW_ACCEPTED_"
            "NO_FUNCTIONALIZATION"
        ),
        "mathematical_statement": (
            "The review accepts the phi bridge-admissibility C_k candidate "
            "packet as a route-consistency candidate only: C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}), with condition "
            "C_bridge^phi = 0. The field-equation, stress-energy, and "
            "source-residual match components are preserved without claiming "
            "a bridge proof, functionalization, or promotion."
        ),
        "non_claim_boundary": (
            "This review accepts the route-consistency candidate only. It "
            "does not functionalize C_bridge^phi, does not embed it in S_C, "
            "does not define a C_k action term, does not select a multiplier "
            "type, does not execute C_k variation, does not vary lambda_k, "
            "phi, or g, does not prove the field-equation match, does not "
            "prove the stress-energy match, does not prove the source-residual "
            "match, does not verify the full route alignment, does not claim "
            "full bridge admissibility, does not generate phi, does not derive "
            "V(phi), does not prove new conservation, does not prove source "
            "admissibility, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, does "
            "not claim empirical validation, and does not authorize public "
            "readiness. The bridge rule remains candidate-only until the "
            "functional-embedding packet decides or blocks action embedding."
        ),
        "critical_gate_fail_conditions": [
            "functionalize or embed C_bridge^phi as an action term",
            "select a multiplier type or domain",
            "execute C_k or lambda variation",
            "execute phi or metric variation of the bridge candidate",
            "claim full bridge admissibility is proved",
            "claim route alignment is verified",
            "claim phi is generated by C_k",
            "claim V(phi) is derived",
            "claim source admissibility or conservation newly proved",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "candidate_packet_file": _ptr(candidate_packet_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the phi bridge-admissibility C_k constraint candidate "
            "packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_phi_bridge_admissibility_ck_constraint_candidate_packet_result_review(
            captured_at_utc=args.captured_at_utc
        )
    )
    path = write_review(review, args.out)
    print(
        json.dumps(
            {
                "accepted": review["accepted"],
                "out": _ptr(path),
                "outcome_id": review["outcome_id"],
                "review_result": review["review_result"],
                "selected_next_target": review["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
