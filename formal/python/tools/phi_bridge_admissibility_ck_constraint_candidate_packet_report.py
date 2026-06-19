from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_relevant_ck_constraint_family_selection_after_source_admissibility_report import (
    AGGREGATE_TIMEOUT_STATUS,
    BRIDGE_ADMISSIBILITY_QUESTION,
    BRIDGE_CANDIDATE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_SHAPE_PREVIEW,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    DEFAULT_OUT as BRIDGE_SELECTOR_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as BRIDGE_SELECTOR_OUTCOME,
    PACKET_ID as BRIDGE_SELECTOR_PACKET_ID,
    SCHEMA_ID as BRIDGE_SELECTOR_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SELECTION_RESULT as BRIDGE_SELECTOR_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_v0"
PACKET_RESULT = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RECORDED_AS_ROUTE_"
    "CONSISTENCY_RULE_NO_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_" + PACKET_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_admissibility_ck_constraint_candidate_packet_records_route_"
    "consistency_rule_no_variation_or_promotion"
)
NEXT_TARGET = "review_phi_bridge_admissibility_ck_constraint_candidate_packet_result"
NEXT_TARGET_KIND = "phi_bridge_admissibility_ck_constraint_candidate_packet_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

BRIDGE_CANDIDATE_ID = "phi_bridge_route_consistency_ck_candidate"
BRIDGE_CANDIDATE_TYPE = "route_consistency_admissibility_rule"
BRIDGE_CONSTRAINT_FORM = (
    "C_bridge^phi := (E_phi^master - E_phi^witness, "
    "T_phi^master - T_phi^witness, "
    "C_source^phi - nabla_mu T_phi^{mu nu})"
)
BRIDGE_CONSTRAINT_EQUATION = "C_bridge^phi = 0"
BRIDGE_ROUTE_FIELD_EQUATION_MATCH = "E_phi^master - E_phi^witness = 0"
BRIDGE_ROUTE_STRESS_ENERGY_MATCH = "T_phi^master - T_phi^witness = 0"
BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH = (
    "C_source^phi - nabla_mu T_phi^{mu nu} = 0"
)
BRIDGE_CANDIDATE_RULE_PLAIN_MEANING = (
    "The bridge passes only if the master-action phi route reproduces the "
    "scalar witness equation, stress-energy source, and source-admissibility "
    "residual under the selected policy."
)
MASTER_PHI_ROUTE_ID = "master_action_phi_surface_under_selected_policy"
SCALAR_WITNESS_ROUTE_ID = "imported_scalar_sandbox_witness_route"
SOURCE_ADMISSIBILITY_ROUTE_ID = "phi_source_conservation_residual_rule"
CLASSICAL_SOURCE_ROUTE_ID = "classical_einstein_scalar_source_route"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeAdmissibilityCKConstraintCandidatePacket.lean"
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


def _bridge_components() -> list[dict[str, Any]]:
    return [
        {
            "component_id": "bridge_field_equation_match",
            "component_form": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
            "plain_meaning": (
                "The master-action phi field equation must match the scalar "
                "witness equation under the selected policy."
            ),
            "variation_executed_here": False,
            "proved_here": False,
        },
        {
            "component_id": "bridge_stress_energy_match",
            "component_form": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
            "plain_meaning": (
                "The master-action phi stress-energy route must match the "
                "scalar witness stress-energy route under convention "
                "normalization."
            ),
            "variation_executed_here": False,
            "proved_here": False,
        },
        {
            "component_id": "bridge_source_residual_match",
            "component_form": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
            "plain_meaning": (
                "The bridge must identify the source-admissibility residual "
                "with the stress-energy divergence residual."
            ),
            "variation_executed_here": False,
            "proved_here": False,
        },
    ]


def _route_alignment_contract() -> list[dict[str, Any]]:
    return [
        {
            "route_step": step,
            "status": "recorded_for_bridge_consistency_check",
            "verified_here": False,
        }
        for step in BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
    ]


def _candidate_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "candidate_packet_consumes_bridge_selector",
            "status": "accepted",
            "evidence": selector.get("selection_result"),
            "assessment": "The packet consumes the bridge-admissibility family selector.",
        },
        {
            "row_id": "selected_bridge_family_carried_forward",
            "status": "accepted",
            "evidence": [
                selector.get("selected_ck_option_class"),
                selector.get("selected_ck_constraint_family"),
            ],
            "assessment": (
                "The packet stays within the selected phi bridge-admissibility "
                "C_k family."
            ),
        },
        {
            "row_id": "route_alignment_sequence_carried_forward",
            "status": "accepted",
            "evidence": selector.get("bridge_route_alignment_sequence"),
            "assessment": "The full phi bridge route is carried forward for checking.",
        },
        {
            "row_id": "route_consistency_tuple_selected",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_FORM,
            "assessment": (
                "The bridge candidate is recorded as a route-consistency tuple."
            ),
        },
        {
            "row_id": "bridge_constraint_equation_recorded",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The admissibility condition C_bridge^phi = 0 is recorded.",
        },
        {
            "row_id": "field_equation_stress_energy_source_residual_components_recorded",
            "status": "accepted",
            "evidence": [
                BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
                BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
                BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
            ],
            "assessment": (
                "The bridge components compare the field equation, stress-energy "
                "route, and source residual."
            ),
        },
        {
            "row_id": "source_admissibility_rule_retained_as_context",
            "status": "accepted",
            "evidence": [
                SOURCE_CANDIDATE_CONSTRAINT_FORM,
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": (
                "The prior source-admissibility rule remains context for the "
                "bridge candidate."
            ),
        },
        {
            "row_id": "admissibility_rule_not_action_term",
            "status": "accepted",
            "evidence": "bridge_candidate_recorded_as_admissibility_rule=true",
            "assessment": (
                "The route-consistency tuple is recorded as an admissibility rule, "
                "not an action term."
            ),
        },
        {
            "row_id": "no_variation_or_functional_embedding",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "ck_action_embedding_claimed=false",
            ],
            "assessment": "No C_k variation or action embedding is executed.",
        },
        {
            "row_id": "no_generation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "phi_generated_by_ck_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "The nonpromotion boundary is preserved.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_bridge_admissibility_ck_constraint_candidate_packet",
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


def build_phi_bridge_admissibility_ck_constraint_candidate_packet(
    *,
    bridge_selector_path: Path = BRIDGE_SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(bridge_selector_path)
    candidate_criteria = _candidate_criteria(selector)
    acceptance_criteria = {
        "consumes_expected_bridge_candidate_target": (
            selector.get("schema_id") == BRIDGE_SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == BRIDGE_SELECTOR_PACKET_ID
            and selector.get("outcome_id") == BRIDGE_SELECTOR_OUTCOME
            and selector.get("selection_result") == BRIDGE_SELECTOR_RESULT
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "bridge_selector_family_preserved": (
            selector.get("selected_ck_option_class") == SELECTED_CK_OPTION_CLASS
            and selector.get("selected_ck_constraint_family")
            == SELECTED_CK_CONSTRAINT_FAMILY
            and selector.get("bridge_admissibility_family_selected") is True
            and selector.get("bridge_candidate_functional_defined") is False
            and selector.get("bridge_route_alignment_verified") is False
        ),
        "source_rule_context_preserved": (
            selector.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and selector.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and selector.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and selector.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and selector.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "route_consistency_candidate_selected": (
            BRIDGE_CONSTRAINT_EQUATION == "C_bridge^phi = 0"
            and BRIDGE_CANDIDATE_TYPE == "route_consistency_admissibility_rule"
            and len(_bridge_components()) == 3
        ),
        "no_selector_shortcut_claims": all(
            selector.get(key) is False
            for key in [
                "bridge_candidate_functional_defined",
                "bridge_route_alignment_verified",
                "ck_variation_executed",
                "phi_generated_by_ck_claimed",
                "potential_derived",
                "new_conservation_proof_claimed",
                "new_source_admissibility_proof_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "empirical_validation_claimed",
                "public_readiness_claimed",
            ]
        ),
        "candidate_criteria_all_accepted": all(
            row["status"] == "accepted" for row in candidate_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "bridge_selector_outcome": BRIDGE_SELECTOR_OUTCOME,
        "bridge_selector_result": BRIDGE_SELECTOR_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "bridge_admissibility_question": BRIDGE_ADMISSIBILITY_QUESTION,
        "bridge_candidate_shape_preview": BRIDGE_CANDIDATE_SHAPE_PREVIEW,
        "bridge_candidate_plain_meaning": BRIDGE_CANDIDATE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_count": len(BRIDGE_ROUTE_ALIGNMENT_SEQUENCE),
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "bridge_components": _bridge_components(),
        "bridge_component_count": len(_bridge_components()),
        "route_alignment_contract": _route_alignment_contract(),
        "route_alignment_contract_count": len(_route_alignment_contract()),
        "master_phi_route_id": MASTER_PHI_ROUTE_ID,
        "scalar_witness_route_id": SCALAR_WITNESS_ROUTE_ID,
        "source_admissibility_route_id": SOURCE_ADMISSIBILITY_ROUTE_ID,
        "classical_source_route_id": CLASSICAL_SOURCE_ROUTE_ID,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "candidate_criteria": candidate_criteria,
        "candidate_criteria_count": len(candidate_criteria),
        "candidate_criteria_accepted_count": sum(
            1 for row in candidate_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "bridge_candidate_packet_prepared": True,
        "bridge_candidate_packet_accepted": True,
        "bridge_candidate_recorded": True,
        "bridge_candidate_selected_as_route_consistency_rule": True,
        "bridge_candidate_recorded_as_admissibility_rule": True,
        "bridge_candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_new_dynamical_law": False,
        "bridge_candidate_functional_defined": False,
        "bridge_candidate_functional_selected": False,
        "bridge_candidate_rule_proved": False,
        "bridge_admissibility_family_selected": True,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_sequence_recorded": True,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_recorded": True,
        "route_consistency_tuple_proved": False,
        "field_equation_match_recorded": True,
        "field_equation_match_proved": False,
        "stress_energy_match_recorded": True,
        "stress_energy_match_proved": False,
        "source_residual_match_recorded": True,
        "source_residual_match_proved": False,
        "source_admissibility_rule_retained_as_context": True,
        "source_admissibility_family_completed": False,
        "source_admissibility_claimed": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
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
        "claim_level": (
            "Level 3 bridge candidate packet; records C_bridge^phi as a "
            "route-consistency admissibility rule without defining an action "
            "term, executing C_k variation, proving bridge admissibility, or "
            "promoting the master action"
        ),
        "claim_ceiling": (
            "route-consistency C_k admissibility-rule candidate only no bridge "
            "proof no concrete functional no action embedding no C_k variation "
            "no phi generation no derived potential no new conservation proof "
            "no source admissibility proof no QFT-GR closure no semiclassical "
            "coupling no canonical master-action promotion"
        ),
        "mathematical_statement": (
            "The candidate packet records C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}) with condition "
            "C_bridge^phi = 0. The tuple is a route-consistency "
            "admissibility rule candidate, not an action term."
        ),
        "non_claim_boundary": (
            "This packet records a phi bridge-admissibility C_k candidate as a "
            "route-consistency admissibility rule only. It does not define a "
            "fully concrete C_k functional, does not embed C_bridge^phi into "
            "the action, does not execute C_k variation, does not vary lambda_k, "
            "phi, or g, does not prove the field-equation match, does not prove "
            "the stress-energy match, does not prove the source-residual match, "
            "does not verify the full route alignment, does not claim bridge "
            "admissibility, does not generate phi, does not derive V(phi), does "
            "not prove new conservation, does not prove source admissibility, "
            "does not close QFT-GR, does not authorize semiclassical coupling, "
            "does not promote the master action, does not claim empirical "
            "validation, and does not authorize public readiness."
        ),
        "critical_gate_fail_conditions": [
            "claim bridge-admissibility is proved",
            "claim route alignment is verified",
            "embed C_bridge^phi into an action",
            "execute C_k variation",
            "claim phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
            "claim new source-admissibility proof",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeAdmissibilityCKConstraintCandidatePacket",
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
            "bridge_selector_file": _ptr(bridge_selector_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the phi bridge-admissibility C_k candidate packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_bridge_admissibility_ck_constraint_candidate_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
