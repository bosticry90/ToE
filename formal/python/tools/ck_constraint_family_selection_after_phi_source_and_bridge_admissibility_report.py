from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_ck_admissibility_rule_family_synthesis_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    CLOSEOUT_RESULT as PHI_CK_SYNTHESIS_CLOSEOUT_RESULT,
    DEFAULT_OUT as PHI_CK_SYNTHESIS_CLOSEOUT_PATH,
    FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    OUTCOME_ID as PHI_CK_SYNTHESIS_CLOSEOUT_OUTCOME,
    PACKET_ID as PHI_CK_SYNTHESIS_CLOSEOUT_PACKET_ID,
    RULE_FAMILY_EPISTEMIC_STATUS,
    SCHEMA_ID as PHI_CK_SYNTHESIS_CLOSEOUT_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = (
    "CK_CONSTRAINT_FAMILY_SELECTION_AFTER_PHI_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_20260619_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_CONSTRAINT_FAMILY_SELECTION_AFTER_PHI_SOURCE_AND_BRIDGE_ADMISSIBILITY_v0"
SELECTION_RESULT = (
    "CK_CONSTRAINT_FAMILY_SELECTION_SELECTS_TRANSPORT_CONSISTENCY_AFTER_PHI_"
    "SOURCE_AND_BRIDGE_ADMISSIBILITY_NO_CK_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "ck_constraint_family_selection_selects_transport_consistency_after_phi_"
    "source_and_bridge_admissibility_no_ck_variation_or_promotion"
)
CONSUMED_TARGET = "select_next_ck_constraint_family_after_phi_source_and_bridge_admissibility"
NEXT_TARGET = "prepare_phi_transport_consistency_ck_constraint_candidate_packet"
NEXT_TARGET_KIND = "phi_transport_consistency_ck_constraint_candidate_packet_preparation"

SELECTED_CK_OPTION_CLASS = "transport_consistency_constraint"
SELECTED_CK_CONSTRAINT_FAMILY = "transport_consistency_ck_constraint_family"
SELECTED_FAMILY_SELECTION_STATUS = (
    "selected_as_next_ck_family_after_phi_source_and_bridge_admissibility"
)
TRANSPORT_CONSISTENCY_QUESTION = (
    "Does the admitted phi object remain coherent as it moves through the "
    "derivation chain?"
)
TRANSPORT_CANDIDATE_SHAPE_PREVIEW = "C_transport^phi = 0"
TRANSPORT_CANDIDATE_PLAIN_MEANING = (
    "The phi route is admitted only if its equation, source, conservation "
    "residual, and regime-facing residual remain compatible as they are "
    "transported through the route."
)
TRANSPORT_CHAIN_STEPS = [
    "ACTION",
    "VARIATION",
    "BRIDGE",
    "OPERATOR",
    "TRANSPORT",
    "RESIDUAL_LAW",
    "REGIME_LIMIT",
]
TRANSPORT_CHAIN_FORM = " -> ".join(TRANSPORT_CHAIN_STEPS)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_CONSTRAINT_FAMILY_SELECTION_AFTER_PHI_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKConstraintFamilySelectionAfterPhiSourceAndBridgeAdmissibility.lean"
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


def _selection_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_phi_source_bridge_family_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": (
                "The selector consumes the live target authorized by the "
                "source/bridge family closeout."
            ),
        },
        {
            "row_id": "source_bridge_family_closeout_accepted",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": (
                "The first synthesized phi/C_k source and bridge family is "
                "accepted as selector context."
            ),
        },
        {
            "row_id": "source_admissibility_rule_retained",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_source^nu[g, phi] = 0 remains the retained source "
                "admissibility rule candidate."
            ),
        },
        {
            "row_id": "bridge_admissibility_rule_retained",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_bridge^phi = 0 remains the retained bridge admissibility "
                "rule candidate."
            ),
        },
        {
            "row_id": "transport_consistency_family_selected",
            "status": "accepted",
            "evidence": SELECTED_CK_CONSTRAINT_FAMILY,
            "assessment": (
                "Transport consistency is selected as the next C_k family "
                "after source and bridge admissibility."
            ),
        },
        {
            "row_id": "transport_question_matches_next_layer",
            "status": "accepted",
            "evidence": TRANSPORT_CONSISTENCY_QUESTION,
            "assessment": (
                "The selected family asks whether the admitted phi object "
                "remains coherent through the route."
            ),
        },
        {
            "row_id": "transport_candidate_shape_only_previewed",
            "status": "accepted",
            "evidence": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
            "assessment": (
                "C_transport^phi = 0 is recorded only as the next packet's "
                "shape preview."
            ),
        },
        {
            "row_id": "transport_chain_recorded_for_next_packet",
            "status": "accepted",
            "evidence": TRANSPORT_CHAIN_FORM,
            "assessment": (
                "The route chain is recorded for the next candidate packet."
            ),
        },
        {
            "row_id": "next_transport_candidate_packet_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next live target is only the phi transport-consistency "
                "candidate packet."
            ),
        },
        {
            "row_id": "no_transport_proof_variation_or_promotion",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "ck_variation_executed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The selector does not prove transport consistency, execute "
                "C_k variation, or promote the master action."
            ),
        },
    ]


def _candidate_family_options() -> list[dict[str, Any]]:
    return [
        {
            "constraint_option_class": "source_admissibility_constraint",
            "constraint_family_id": "phi_source_admissibility_constraint_family",
            "selection_status": "closed_as_retained_context_not_reselected",
            "candidate_shape": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "candidate_packet_target": None,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
        {
            "constraint_option_class": "bridge_admissibility_constraint",
            "constraint_family_id": "phi_bridge_admissibility_constraint_family",
            "selection_status": "closed_as_retained_context_not_reselected",
            "candidate_shape": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "candidate_packet_target": None,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
        {
            "constraint_option_class": SELECTED_CK_OPTION_CLASS,
            "constraint_family_id": SELECTED_CK_CONSTRAINT_FAMILY,
            "selection_status": SELECTED_FAMILY_SELECTION_STATUS,
            "candidate_packet_target": NEXT_TARGET,
            "recommended_candidate_shape_preview": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "ck_constraint_family_selection_after_phi_source_and_bridge_admissibility"
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


def build_ck_constraint_family_selection_after_phi_source_and_bridge_admissibility(
    *,
    phi_ck_synthesis_closeout_path: Path = PHI_CK_SYNTHESIS_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(phi_ck_synthesis_closeout_path)
    selection_criteria = _selection_criteria(closeout)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            closeout.get("schema_id") == PHI_CK_SYNTHESIS_CLOSEOUT_SCHEMA_ID
            and closeout.get("packet_id") == PHI_CK_SYNTHESIS_CLOSEOUT_PACKET_ID
            and closeout.get("outcome_id") == PHI_CK_SYNTHESIS_CLOSEOUT_OUTCOME
            and closeout.get("closeout_result") == PHI_CK_SYNTHESIS_CLOSEOUT_RESULT
            and closeout.get("selected_next_target") == CONSUMED_TARGET
            and closeout.get("accepted") is True
        ),
        "source_and_bridge_family_preserved": (
            closeout.get("family_classification")
            == FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION
            and closeout.get("family_epistemic_status")
            == RULE_FAMILY_EPISTEMIC_STATUS
            and closeout.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and closeout.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and closeout.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and closeout.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and closeout.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and closeout.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and closeout.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_route_components_preserved": (
            closeout.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and closeout.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and closeout.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "source_bridge_family_boundary_preserved": (
            closeout.get("both_rules_admissibility_only") is True
            and closeout.get("both_rules_rule_candidates") is True
            and closeout.get("both_rules_not_action_terms") is True
            and closeout.get("both_rules_not_dynamical_laws") is True
            and closeout.get("neither_rule_derives_phi") is True
            and closeout.get("neither_rule_derives_v_phi") is True
        ),
        "transport_selection_is_selector_only": (
            SELECTED_CK_OPTION_CLASS == "transport_consistency_constraint"
            and SELECTED_CK_CONSTRAINT_FAMILY
            == "transport_consistency_ck_constraint_family"
            and NEXT_TARGET
            == "prepare_phi_transport_consistency_ck_constraint_candidate_packet"
        ),
        "no_shortcut_claims_in_closeout": all(
            closeout.get(key) is False
            for key in [
                "transport_consistency_family_selected",
                "constraint_as_action_term_selected",
                "dynamical_action_embedding_selected",
                "ck_action_embedding_claimed",
                "ck_variation_executed",
                "ck_variation_authorized",
                "bridge_admissibility_proved",
                "route_alignment_verified",
                "source_admissibility_proved",
                "source_conservation_proved",
                "native_phi_derivation_claimed",
                "phi_generated_by_ck_claimed",
                "v_phi_derivation_claimed",
                "derived_v_phi_claimed",
                "potential_derived",
                "qft_gr_closure_claimed",
                "qft_gr_solved",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "semiclassical_einstein_equation_derived",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            closeout.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and closeout.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and closeout.get("full_toeformal_aggregate_passed") is False
            and closeout.get("full_toeformal_aggregate_failed") is False
            and closeout.get("full_toeformal_aggregate_timed_out") is False
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_PHI_SOURCE_AND_BRIDGE_ADMISSIBILITY"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_PHI_SOURCE_AND_BRIDGE_"
            "ADMISSIBILITY"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_CONSTRAINT_FAMILY_SELECTION_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "phi_ck_synthesis_closeout_packet_id": PHI_CK_SYNTHESIS_CLOSEOUT_PACKET_ID,
        "phi_ck_synthesis_closeout_outcome": PHI_CK_SYNTHESIS_CLOSEOUT_OUTCOME,
        "phi_ck_synthesis_closeout_result": PHI_CK_SYNTHESIS_CLOSEOUT_RESULT,
        "family_classification": FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION,
        "family_epistemic_status": RULE_FAMILY_EPISTEMIC_STATUS,
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
        "phi_ck_admissibility_rule_family_count": 2,
        "closed_phi_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
        ],
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "selected_family_selection_status": SELECTED_FAMILY_SELECTION_STATUS,
        "transport_consistency_question": TRANSPORT_CONSISTENCY_QUESTION,
        "transport_candidate_shape_preview": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
        "transport_candidate_plain_meaning": TRANSPORT_CANDIDATE_PLAIN_MEANING,
        "transport_chain_form": TRANSPORT_CHAIN_FORM,
        "transport_chain_steps": TRANSPORT_CHAIN_STEPS,
        "transport_chain_step_count": len(TRANSPORT_CHAIN_STEPS),
        "candidate_family_options": _candidate_family_options(),
        "candidate_family_option_count": 3,
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_target_prepared": True,
        "selector_target_accepted": True,
        "selection_executed": True,
        "transport_consistency_family_selected": True,
        "transport_consistency_candidate_packet_authorized": True,
        "transport_consistency_candidate_packet_prepared": False,
        "transport_candidate_shape_preview_recorded": True,
        "transport_chain_recorded": True,
        "source_and_bridge_family_retained_as_context": True,
        "source_admissibility_rule_retained_as_context": True,
        "bridge_admissibility_rule_retained_as_context": True,
        "source_admissibility_family_reselected": False,
        "bridge_admissibility_family_reselected": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "transport_proof_claimed": False,
        "transport_consistency_proved": False,
        "transport_chain_compatibility_proved": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "candidate_action_insertion_executed": False,
        "constraint_as_action_term_selected": False,
        "constraint_term_selected": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_executed": False,
        "phi_variation_executed": False,
        "native_phi_derivation_claimed": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "native_generation_theorem_claimed": False,
        "v_phi_derivation_claimed": False,
        "derived_v_phi_claimed": False,
        "potential_derived": False,
        "new_conservation_proof_claimed": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "toe_native_matter_derivation_claimed": False,
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
            "Level 3 selector; selects transport consistency as the next C_k "
            "constraint family after the closed phi source and bridge "
            "admissibility family without defining C_transport^phi, executing "
            "variation, proving transport, or promoting the master action"
        ),
        "claim_ceiling": (
            "selector-only C_k family choice no transport candidate packet yet "
            "no C_transport functional no transport proof no C_k variation no "
            "action embedding no native phi generation no V(phi) derivation no "
            "new conservation proof no QFT-GR closure no semiclassical coupling "
            "no master-action promotion"
        ),
        "mathematical_statement": (
            "The selector retains the closed source-admissibility rule "
            "C_source^nu[g, phi] = 0 and bridge-admissibility rule "
            "C_bridge^phi = 0 as context, then selects "
            "transport_consistency_ck_constraint_family as the next C_k family. "
            "The next packet may attempt a candidate shaped like "
            "C_transport^phi = 0 across ACTION -> VARIATION -> BRIDGE -> "
            "OPERATOR -> TRANSPORT -> RESIDUAL_LAW -> REGIME_LIMIT, but no "
            "such functional is defined here."
        ),
        "non_claim_boundary": (
            "This selector only chooses transport_consistency_ck_constraint_family "
            "as the next C_k family after the closed phi source and bridge "
            "admissibility family. It preserves C_source^nu[g, phi] = 0 and "
            "C_bridge^phi = 0 as admissibility-only rule candidates. It does "
            "not prepare the transport candidate packet, does not define "
            "C_transport^phi, does not prove transport consistency, does not "
            "prove route-chain compatibility, does not embed C_k in an action, "
            "does not execute C_k variation, does not generate phi, does not "
            "derive V(phi), does not prove new conservation, does not close "
            "QFT-GR, does not authorize semiclassical coupling, does not "
            "promote the master action, does not claim empirical validation, "
            "and does not authorize public readiness. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this selector."
        ),
        "critical_gate_fail_conditions": [
            "drop C_source^nu[g, phi] = 0 context",
            "drop C_bridge^phi = 0 context",
            "fail to select transport_consistency_ck_constraint_family",
            "prepare the transport packet inside this selector",
            "define C_transport^phi as a functional inside this selector",
            "claim transport consistency is proved",
            "execute C_k variation",
            "embed C_k in the action",
            "claim native phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
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
            "ToeFormal.Derivation.CKConstraintFamilySelectionAfterPhiSourceAndBridgeAdmissibility",
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
            "phi_ck_synthesis_closeout_file": _ptr(phi_ck_synthesis_closeout_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_selection(selection: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the C_k family selector after phi source and bridge admissibility."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    selection = (
        build_ck_constraint_family_selection_after_phi_source_and_bridge_admissibility(
            captured_at_utc=args.captured_at_utc
        )
    )
    path = write_selection(selection, args.out)
    print(
        json.dumps(
            {
                "accepted": selection["accepted"],
                "out": _ptr(path),
                "selected_next_target": selection["selected_next_target"],
                "selection_result": selection["selection_result"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
