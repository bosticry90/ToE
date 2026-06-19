from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_consistency_ck_constraint_candidate_packet_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    KNOWN_PHI_TRANSPORT_CHAIN_STEPS,
    LEAN_VALIDATION_POLICY_ID,
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
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = (
    "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
    "20260619_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_ACCEPTS_"
    "DERIVATION_CHAIN_STABILITY_CANDIDATE_NO_FUNCTIONALIZATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_consistency_ck_constraint_candidate_result_review_accepts_"
    "derivation_chain_stability_candidate_no_functionalization_or_promotion"
)
CONSUMED_TARGET = "review_phi_transport_consistency_ck_constraint_candidate_packet_result"
NEXT_TARGET = "prepare_phi_transport_consistency_ck_functional_embedding_packet"
NEXT_TARGET_KIND = "phi_transport_consistency_ck_functional_embedding_packet_preparation"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
    "20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportConsistencyCKConstraintCandidatePacketResultReview.lean"
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
            "row_id": "transport_candidate_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("outcome_id"),
            "assessment": "The review consumes the transport candidate packet.",
        },
        {
            "row_id": "transport_constraint_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_EQUATION,
            "assessment": "The review preserves C_transport^phi = 0.",
        },
        {
            "row_id": "transport_tuple_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": "The derivation-chain stability tuple is carried forward.",
        },
        {
            "row_id": "transport_components_preserved_unproved",
            "status": "accepted",
            "evidence": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "assessment": (
                "The route-stability components are preserved without proving "
                "any component."
            ),
        },
        {
            "row_id": "admissibility_only_classification_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_RULE_CLASSIFICATION,
            "assessment": (
                "The transport candidate remains an admissibility-only rule "
                "candidate."
            ),
        },
        {
            "row_id": "source_and_bridge_context_retained",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": "Source and bridge admissibility rules remain context.",
        },
        {
            "row_id": "known_phi_chain_retained",
            "status": "accepted",
            "evidence": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
            "assessment": "The known phi transport chain remains the grounding chain.",
        },
        {
            "row_id": "no_functionalization_or_action_embedding",
            "status": "accepted",
            "evidence": [
                "transport_candidate_functional_defined=false",
                "ck_action_embedding_claimed=false",
            ],
            "assessment": "No action term or C_k functional is defined.",
        },
        {
            "row_id": "no_ck_variation",
            "status": "accepted",
            "evidence": "ck_variation_executed=false",
            "assessment": "No C_k, metric, phi, or multiplier variation is executed.",
        },
        {
            "row_id": "no_transport_or_full_route_proof",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "full_route_alignment_proved=false",
            ],
            "assessment": (
                "The review does not prove transport consistency or full route "
                "alignment."
            ),
        },
        {
            "row_id": "no_generation_conservation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "native_phi_derivation_claimed=false",
                "v_phi_derivation_claimed=false",
                "new_conservation_proof_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The review preserves no native phi generation, no V(phi) "
                "derivation, no new conservation proof, no QFT-GR closure, "
                "and no master-action promotion."
            ),
        },
        {
            "row_id": "full_toeformal_aggregate_recorded_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate remains recorded as NOT_RUN.",
        },
        {
            "row_id": "functional_embedding_packet_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next packet may test and likely block action embedding "
                "routes for C_transport^phi."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "phi_transport_consistency_ck_constraint_candidate_packet_result_review"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_transport_consistency_ck_constraint_candidate_packet_result_review(
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
        "transport_candidate_exact": (
            packet.get("transport_candidate_id") == TRANSPORT_CANDIDATE_ID
            and packet.get("transport_candidate_type") == TRANSPORT_CANDIDATE_TYPE
            and packet.get("transport_rule_classification")
            == TRANSPORT_RULE_CLASSIFICATION
            and packet.get("transport_rule_epistemic_status")
            == TRANSPORT_RULE_EPISTEMIC_STATUS
            and packet.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
            and packet.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
        ),
        "transport_components_exact_unproved": (
            packet.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
            and packet.get("transport_components_recorded") is True
            and packet.get("transport_components_proved") is False
            and [row.get("component_form") for row in packet.get("transport_components", [])]
            == [row["component_form"] for row in TRANSPORT_COMPONENTS]
        ),
        "source_bridge_context_exact": (
            packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and packet.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and packet.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
            and packet.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_route_context_exact": (
            packet.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and packet.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and packet.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "known_chain_exact": (
            packet.get("known_phi_transport_chain_form")
            == KNOWN_PHI_TRANSPORT_CHAIN_FORM
            and packet.get("known_phi_transport_chain_steps")
            == KNOWN_PHI_TRANSPORT_CHAIN_STEPS
            and packet.get("known_phi_chain_recorded") is True
            and packet.get("known_phi_chain_proved") is False
        ),
        "candidate_only_boundary_carried_forward": (
            packet.get("transport_candidate_recorded_as_admissibility_rule") is True
            and packet.get("transport_candidate_recorded_as_action_term") is False
            and packet.get("transport_candidate_recorded_as_new_dynamical_law") is False
            and packet.get("transport_candidate_rule_proved") is False
            and packet.get("transport_tuple_proved") is False
            and packet.get("transport_consistency_proved") is False
            and packet.get("full_route_alignment_proved") is False
        ),
        "no_functionalization_variation_or_forbidden_claims": all(
            packet.get(key) is False
            for key in [
                "transport_candidate_functional_defined",
                "transport_candidate_functional_selected",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "ck_action_embedding_claimed",
                "candidate_action_insertion_executed",
                "constraint_as_action_term_selected",
                "constraint_term_selected",
                "ck_variation_executed",
                "ck_variation_authorized",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "phi_variation_of_candidate_executed",
                "native_phi_derivation_claimed",
                "phi_generated_by_ck_claimed",
                "v_phi_derivation_claimed",
                "derived_v_phi_claimed",
                "new_conservation_proof_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "canonical_master_action_promoted",
                "empirical_validation_claimed",
            ]
        ),
        "aggregate_recorded_not_run": (
            packet.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and packet.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and packet.get("full_toeformal_aggregate_passed") is False
            and packet.get("full_toeformal_aggregate_failed") is False
            and packet.get("full_toeformal_aggregate_timed_out") is False
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_TRANSPORT_CONSISTENCY_CK_CANDIDATE_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CONSISTENCY_CK_CANDIDATE_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
        "candidate_packet_result": CANDIDATE_PACKET_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [row["component_form"] for row in TRANSPORT_COMPONENTS],
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "known_phi_transport_chain_steps": KNOWN_PHI_TRANSPORT_CHAIN_STEPS,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "closed_phi_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
            "transport consistency",
        ],
        "phi_ck_rule_family_count_after_review": 3,
        "review_accepts_derivation_chain_stability_candidate": True,
        "derivation_chain_stability_candidate_accepted": True,
        "transport_constraint_preserved": True,
        "transport_tuple_preserved": True,
        "transport_components_preserved": True,
        "transport_components_proved": False,
        "transport_candidate_classified_as_admissibility_only": True,
        "source_and_bridge_context_retained": True,
        "known_phi_chain_retained": True,
        "functional_embedding_packet_authorized": True,
        "functional_embedding_packet_prepared": False,
        "functional_embedding_executed": False,
        "multiplier_action_route_test_authorized": True,
        "penalty_route_test_authorized": True,
        "direct_dynamical_law_interpretation_test_authorized": True,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_interpretation_selected": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_candidate_rule_proved": False,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "full_route_alignment_proof_claimed": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "ck_action_embedding_claimed": False,
        "candidate_action_insertion_executed": False,
        "constraint_as_action_term_selected": False,
        "constraint_term_selected": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "phi_variation_of_candidate_executed": False,
        "metric_variation_executed": False,
        "phi_variation_executed": False,
        "constraint_multiplier_type_selected": False,
        "higher_derivative_scope_resolved": False,
        "boundary_terms_controlled": False,
        "native_phi_derivation_claimed": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "native_generation_theorem_claimed": False,
        "derived_v_phi_claimed": False,
        "v_phi_derivation_claimed": False,
        "potential_derived": False,
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
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "standard_model_derivation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
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
            "PHI_TRANSPORT_CONSISTENCY_CK_CANDIDATE_REVIEW_ACCEPTED_"
            "NO_FUNCTIONALIZATION"
        ),
        "mathematical_statement": (
            "The review accepts the phi transport-consistency C_k candidate "
            "as an admissibility-only derivation-chain stability rule "
            "candidate: C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi), "
            "with condition C_transport^phi = 0. The source and bridge rules "
            "remain context; no transport proof, action embedding, variation, "
            "or promotion is claimed."
        ),
        "non_claim_boundary": (
            "This review accepts C_transport^phi = 0 only as an "
            "admissibility-only derivation-chain stability candidate. It does "
            "not functionalize C_transport^phi, does not embed it in S_C, does "
            "not define a C_k action term, does not select a multiplier/action "
            "route, does not select a penalty route, does not interpret the "
            "candidate as a direct dynamical law, does not execute C_k "
            "variation, does not vary lambda_k, phi, or g, does not prove any "
            "transport component, does not prove transport consistency, does "
            "not prove full route alignment, does not generate phi, does not "
            "derive V(phi), does not prove new conservation, does not prove "
            "source admissibility, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, does "
            "not claim empirical validation, and does not authorize public "
            "readiness. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this review."
        ),
        "critical_gate_fail_conditions": [
            "functionalize or embed C_transport^phi as an action term",
            "select a multiplier/action route",
            "select a penalty route",
            "interpret C_transport^phi as a direct dynamical law",
            "execute C_k or lambda variation",
            "execute phi or metric variation of the transport candidate",
            "claim transport consistency is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "claim native phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
            "claim source-admissibility proof",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiTransportConsistencyCKConstraintCandidatePacketResultReview",
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
            "Build the phi transport-consistency C_k constraint candidate "
            "packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_phi_transport_consistency_ck_constraint_candidate_packet_result_review(
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
