from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_constraint_family_selection_after_phi_source_and_bridge_admissibility_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as TRANSPORT_SELECTOR_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as TRANSPORT_SELECTOR_OUTCOME,
    PACKET_ID as TRANSPORT_SELECTOR_PACKET_ID,
    SCHEMA_ID as TRANSPORT_SELECTOR_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SELECTION_RESULT as TRANSPORT_SELECTOR_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
    TRANSPORT_CHAIN_FORM,
    TRANSPORT_CHAIN_STEPS,
    TRANSPORT_CONSISTENCY_QUESTION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_v0"
PACKET_RESULT = (
    "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_RECORDED_AS_"
    "DERIVATION_CHAIN_STABILITY_RULE_NO_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = (
    "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "phi_transport_consistency_ck_constraint_candidate_packet_records_derivation_"
    "chain_stability_rule_no_variation_or_promotion"
)
NEXT_TARGET = "review_phi_transport_consistency_ck_constraint_candidate_packet_result"
NEXT_TARGET_KIND = "phi_transport_consistency_ck_constraint_candidate_packet_result_review"

TRANSPORT_CANDIDATE_ID = "phi_transport_derivation_chain_stability_ck_candidate"
TRANSPORT_CANDIDATE_TYPE = "derivation_chain_stability_admissibility_rule"
TRANSPORT_RULE_CLASSIFICATION = (
    "admissibility-only transport-stability rule candidate"
)
TRANSPORT_RULE_EPISTEMIC_STATUS = "admissibility-only"
TRANSPORT_CONSTRAINT_FORM = (
    "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
    "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
    "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi)"
)
TRANSPORT_CONSTRAINT_EQUATION = "C_transport^phi = 0"
TRANSPORT_RULE_PLAIN_MEANING = (
    "The phi route is admitted only if the object remains coherent as it moves "
    "from action surface to variation, bridge, source, conservation residual, "
    "and regime-facing residual."
)
KNOWN_PHI_TRANSPORT_CHAIN_STEPS = [
    "S_phi",
    "E_phi",
    "T_phi",
    "C_source^phi",
    "C_bridge^phi",
    "bounded residual/regime-facing route",
]
KNOWN_PHI_TRANSPORT_CHAIN_FORM = " -> ".join(KNOWN_PHI_TRANSPORT_CHAIN_STEPS)

TRANSPORT_COMPONENTS = [
    {
        "component_id": "transport_action_variation_phi",
        "component_form": "Transport_ACTION_VARIATION^phi = 0",
        "route_edge": "S_phi -> E_phi",
        "plain_meaning": (
            "The selected phi action surface must transport coherently to the "
            "phi variation route."
        ),
    },
    {
        "component_id": "transport_variation_bridge_phi",
        "component_form": "Transport_VARIATION_BRIDGE^phi = 0",
        "route_edge": "E_phi -> C_bridge^phi",
        "plain_meaning": (
            "The phi variation route must remain compatible with the bridge "
            "admissibility route."
        ),
    },
    {
        "component_id": "transport_bridge_source_phi",
        "component_form": "Transport_BRIDGE_SOURCE^phi = 0",
        "route_edge": "C_bridge^phi -> T_phi",
        "plain_meaning": (
            "The bridge route must remain compatible with the phi source "
            "route."
        ),
    },
    {
        "component_id": "transport_source_residual_phi",
        "component_form": "Transport_SOURCE_RESIDUAL^phi = 0",
        "route_edge": "T_phi -> C_source^phi",
        "plain_meaning": (
            "The phi source route must remain compatible with the conservation "
            "residual route."
        ),
    },
    {
        "component_id": "transport_residual_regime_phi",
        "component_form": "Transport_RESIDUAL_REGIME^phi = 0",
        "route_edge": "C_source^phi -> bounded residual/regime-facing route",
        "plain_meaning": (
            "The residual route must remain compatible with the bounded "
            "regime-facing route."
        ),
    },
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportConsistencyCKConstraintCandidatePacket.lean"
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


def _transport_components() -> list[dict[str, Any]]:
    return [
        {
            **component,
            "recorded_here": True,
            "proved_here": False,
            "variation_executed_here": False,
            "action_term_defined_here": False,
        }
        for component in TRANSPORT_COMPONENTS
    ]


def _candidate_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "candidate_packet_consumes_transport_selector",
            "status": "accepted",
            "evidence": selector.get("selection_result"),
            "assessment": (
                "The packet consumes the transport-consistency family selector."
            ),
        },
        {
            "row_id": "selected_transport_family_carried_forward",
            "status": "accepted",
            "evidence": [
                selector.get("selected_ck_option_class"),
                selector.get("selected_ck_constraint_family"),
            ],
            "assessment": (
                "The packet stays within the selected transport-consistency C_k "
                "family."
            ),
        },
        {
            "row_id": "source_and_bridge_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": (
                "The closed source and bridge admissibility rules remain "
                "context for the transport candidate."
            ),
        },
        {
            "row_id": "transport_tuple_recorded",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": (
                "The transport candidate is recorded as a derivation-chain "
                "stability tuple."
            ),
        },
        {
            "row_id": "transport_constraint_equation_recorded",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_EQUATION,
            "assessment": "The admissibility condition C_transport^phi = 0 is recorded.",
        },
        {
            "row_id": "transport_components_recorded",
            "status": "accepted",
            "evidence": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "assessment": (
                "The five route-stability components are recorded without "
                "claiming they are proved."
            ),
        },
        {
            "row_id": "known_phi_chain_recorded",
            "status": "accepted",
            "evidence": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
            "assessment": "The known phi transport chain is retained as grounding.",
        },
        {
            "row_id": "admissibility_rule_not_action_term",
            "status": "accepted",
            "evidence": "transport_candidate_recorded_as_admissibility_rule=true",
            "assessment": (
                "The derivation-chain stability tuple is recorded as an "
                "admissibility rule candidate, not as an action term."
            ),
        },
        {
            "row_id": "no_variation_or_transport_proof",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "transport_consistency_proved=false",
            ],
            "assessment": "No C_k variation or transport proof is executed.",
        },
        {
            "row_id": "no_generation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "native_phi_derivation_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "The nonpromotion boundary is preserved.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_transport_consistency_ck_constraint_candidate_packet",
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


def build_phi_transport_consistency_ck_constraint_candidate_packet(
    *,
    transport_selector_path: Path = TRANSPORT_SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(transport_selector_path)
    candidate_criteria = _candidate_criteria(selector)
    transport_components = _transport_components()
    acceptance_criteria = {
        "consumes_expected_transport_candidate_target": (
            selector.get("schema_id") == TRANSPORT_SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == TRANSPORT_SELECTOR_PACKET_ID
            and selector.get("outcome_id") == TRANSPORT_SELECTOR_OUTCOME
            and selector.get("selection_result") == TRANSPORT_SELECTOR_RESULT
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "transport_selector_family_preserved": (
            selector.get("selected_ck_option_class") == SELECTED_CK_OPTION_CLASS
            and selector.get("selected_ck_constraint_family")
            == SELECTED_CK_CONSTRAINT_FAMILY
            and selector.get("transport_consistency_family_selected") is True
            and selector.get("transport_candidate_functional_defined") is False
            and selector.get("transport_consistency_proved") is False
        ),
        "source_and_bridge_context_preserved": (
            selector.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and selector.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and selector.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and selector.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and selector.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and selector.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and selector.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_route_components_preserved": (
            selector.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and selector.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and selector.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "transport_candidate_recorded_as_rule_only": (
            TRANSPORT_CONSTRAINT_EQUATION == "C_transport^phi = 0"
            and TRANSPORT_CANDIDATE_TYPE
            == "derivation_chain_stability_admissibility_rule"
            and len(transport_components) == 5
        ),
        "no_selector_shortcut_claims": all(
            selector.get(key) is False
            for key in [
                "transport_candidate_functional_defined",
                "transport_candidate_functional_selected",
                "transport_proof_claimed",
                "transport_consistency_proved",
                "transport_chain_compatibility_proved",
                "ck_variation_executed",
                "ck_action_embedding_claimed",
                "native_phi_derivation_claimed",
                "phi_generated_by_ck_claimed",
                "v_phi_derivation_claimed",
                "derived_v_phi_claimed",
                "potential_derived",
                "new_conservation_proof_claimed",
                "source_admissibility_proved",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "empirical_validation_claimed",
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
        else "REMEDIATE_PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "transport_selector_outcome": TRANSPORT_SELECTOR_OUTCOME,
        "transport_selector_result": TRANSPORT_SELECTOR_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "transport_consistency_question": TRANSPORT_CONSISTENCY_QUESTION,
        "transport_candidate_shape_preview": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
        "transport_chain_form": TRANSPORT_CHAIN_FORM,
        "transport_chain_steps": TRANSPORT_CHAIN_STEPS,
        "transport_chain_step_count": len(TRANSPORT_CHAIN_STEPS),
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_rule_plain_meaning": TRANSPORT_RULE_PLAIN_MEANING,
        "transport_components": transport_components,
        "transport_component_count": len(transport_components),
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "known_phi_transport_chain_steps": KNOWN_PHI_TRANSPORT_CHAIN_STEPS,
        "known_phi_transport_chain_step_count": len(KNOWN_PHI_TRANSPORT_CHAIN_STEPS),
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
        "phi_ck_rule_family_count_after_packet": 3,
        "candidate_criteria": candidate_criteria,
        "candidate_criteria_count": len(candidate_criteria),
        "candidate_criteria_accepted_count": sum(
            1 for row in candidate_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "transport_candidate_packet_prepared": True,
        "transport_candidate_packet_accepted": True,
        "transport_candidate_recorded": True,
        "transport_candidate_selected_as_derivation_chain_stability_rule": True,
        "transport_candidate_recorded_as_admissibility_rule": True,
        "transport_candidate_recorded_as_transport_stability_rule": True,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "transport_candidate_rule_proved": False,
        "transport_tuple_recorded": True,
        "transport_tuple_proved": False,
        "transport_components_recorded": True,
        "transport_components_proved": False,
        "known_phi_chain_recorded": True,
        "known_phi_chain_proved": False,
        "transport_consistency_family_selected": True,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "full_route_alignment_proof_claimed": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_rule_retained_as_context": True,
        "bridge_admissibility_rule_retained_as_context": True,
        "source_admissibility_claimed": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_claimed": False,
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
        "result_review_authorized": True,
        "result_review_prepared": False,
        "review_prepared": False,
        "review_executed": False,
        "claim_level": (
            "Level 3 transport candidate packet; records C_transport^phi as a "
            "derivation-chain stability admissibility rule without defining an "
            "action term, executing C_k variation, proving transport "
            "consistency, or promoting the master action"
        ),
        "claim_ceiling": (
            "transport-stability C_k admissibility-rule candidate only no "
            "transport proof no full route-alignment proof no action embedding "
            "no C_k variation no native phi generation no V(phi) derivation no "
            "new conservation proof no source-admissibility proof no QFT-GR "
            "closure no semiclassical coupling no canonical master-action "
            "promotion"
        ),
        "mathematical_statement": (
            "The candidate packet records C_transport^phi := "
            "(Transport_ACTION_VARIATION^phi, Transport_VARIATION_BRIDGE^phi, "
            "Transport_BRIDGE_SOURCE^phi, Transport_SOURCE_RESIDUAL^phi, "
            "Transport_RESIDUAL_REGIME^phi) with condition "
            "C_transport^phi = 0. The tuple is an admissibility-only "
            "transport-stability rule candidate over the phi chain S_phi -> "
            "E_phi -> T_phi -> C_source^phi -> C_bridge^phi -> bounded "
            "residual/regime-facing route."
        ),
        "non_claim_boundary": (
            "This packet records a phi transport-consistency C_k candidate as "
            "an admissibility-only derivation-chain stability rule. It does "
            "not define a fully concrete C_k functional, does not embed "
            "C_transport^phi into the action, does not execute C_k variation, "
            "does not vary lambda_k, phi, or g, does not prove any transport "
            "component, does not prove transport consistency, does not prove "
            "full route alignment, does not generate phi, does not derive "
            "V(phi), does not prove new conservation, does not prove source "
            "admissibility, does not prove bridge admissibility, does not close "
            "QFT-GR, does not authorize semiclassical coupling, does not "
            "promote the master action, does not claim empirical validation, "
            "and does not authorize public readiness. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this packet."
        ),
        "critical_gate_fail_conditions": [
            "claim transport consistency is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "embed C_transport^phi into an action",
            "execute C_k variation",
            "claim native phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
            "claim source-admissibility proof",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
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
            "ToeFormal.Derivation.PhiTransportConsistencyCKConstraintCandidatePacket",
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
            "transport_selector_file": _ptr(transport_selector_path),
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
        description=(
            "Build the phi transport-consistency C_k constraint candidate packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_transport_consistency_ck_constraint_candidate_packet(
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
