from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_admissibility_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_CONSTRAINT_FORM as SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    AGGREGATE_TIMEOUT_STATUS,
    CANDIDATE_CONSTRAINT_EQUATION as SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM as SOURCE_CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID as SOURCE_CANDIDATE_CONSTRAINT_ID,
    CLOSEOUT_RESULT as SOURCE_RULE_CLOSEOUT_RESULT,
    DEFAULT_OUT as SOURCE_RULE_CLOSEOUT_PATH,
    FIRST_RULE_CLASSIFICATION,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as SOURCE_RULE_CLOSEOUT_OUTCOME,
    PACKET_ID as SOURCE_RULE_CLOSEOUT_PACKET_ID,
    RESIDUAL_IDENTITY_FORM,
    SCHEMA_ID as SOURCE_RULE_CLOSEOUT_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY as SOURCE_SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS as SOURCE_SELECTED_CK_OPTION_CLASS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_v0"
)
SELECTION_RESULT = (
    "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_SELECTS_BRIDGE_"
    "ADMISSIBILITY_AFTER_SOURCE_ADMISSIBILITY_NO_CK_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "phi_relevant_ck_constraint_family_selection_selects_bridge_admissibility_"
    "after_source_admissibility_no_ck_variation_or_promotion"
)
NEXT_TARGET = "prepare_phi_bridge_admissibility_ck_constraint_candidate_packet"
NEXT_TARGET_KIND = "phi_bridge_admissibility_ck_constraint_candidate_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

SELECTED_CK_OPTION_CLASS = "bridge_admissibility_constraint"
SELECTED_CK_CONSTRAINT_FAMILY = "phi_bridge_admissibility_constraint_family"
SELECTED_FAMILY_SELECTION_STATUS = "selected_as_next_abstract_phi_relevant_family"
PREVIOUS_CK_OPTION_CLASS = SOURCE_SELECTED_CK_OPTION_CLASS
PREVIOUS_CK_CONSTRAINT_FAMILY = SOURCE_SELECTED_CK_CONSTRAINT_FAMILY
PREVIOUS_FAMILY_STATUS = "closed_as_first_rule_candidate_reference_not_reselected"

BRIDGE_ADMISSIBILITY_QUESTION = (
    "Does the phi route correctly connect the scalar field, the QFT-GR source "
    "ladder, and the master-action structure?"
)
SOURCE_ADMISSIBILITY_QUESTION = "Can phi act as a gravity source?"
BRIDGE_CANDIDATE_SHAPE_PREVIEW = "C_bridge^phi = 0"
BRIDGE_CANDIDATE_PLAIN_MEANING = (
    "The phi route is admitted only if the master-action phi surface, the "
    "scalar witness route, and the QFT-GR source route agree under the selected "
    "policy."
)
BRIDGE_ROUTE_ALIGNMENT_SEQUENCE = [
    "master-action phi surface",
    "selected phi policy",
    "scalar variation",
    "scalar stress-energy",
    "conservation residual",
    "source-admissibility rule",
    "classical gravity source route",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiRelevantCKConstraintFamilySelectionAfterSourceAdmissibility.lean"
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


def _candidate_family_options() -> list[dict[str, Any]]:
    return [
        {
            "constraint_option_class": PREVIOUS_CK_OPTION_CLASS,
            "constraint_family_id": PREVIOUS_CK_CONSTRAINT_FAMILY,
            "selection_status": PREVIOUS_FAMILY_STATUS,
            "phi_relevance": "already_tested_at_rule_candidate_level",
            "selection_reason": (
                "Source-admissibility already produced the preserved "
                "conservation-residual rule candidate C_source^nu[g, phi] = 0, "
                "so it is retained as context rather than reselected."
            ),
            "candidate_packet_target": None,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
        {
            "constraint_option_class": SELECTED_CK_OPTION_CLASS,
            "constraint_family_id": SELECTED_CK_CONSTRAINT_FAMILY,
            "selection_status": SELECTED_FAMILY_SELECTION_STATUS,
            "phi_relevance": "highest_next",
            "selection_reason": (
                "After source-admissibility asks whether phi may source "
                "gravity, bridge-admissibility is the next seam question: "
                "whether the phi route aligns the master-action surface, the "
                "selected scalar policy, and the QFT-GR source ladder."
            ),
            "candidate_packet_target": NEXT_TARGET,
            "recommended_candidate_shape_preview": BRIDGE_CANDIDATE_SHAPE_PREVIEW,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
    ]


def _selection_criteria(source_closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_authorized_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": (
                "The selector consumes the active target authorized by the "
                "source-admissibility rule closeout."
            ),
        },
        {
            "row_id": "source_admissibility_rule_closeout_accepted",
            "status": "accepted",
            "evidence": source_closeout.get("closeout_result"),
            "assessment": (
                "The first phi-relevant C_k source-admissibility rule candidate "
                "is preserved as accepted context."
            ),
        },
        {
            "row_id": "source_admissibility_not_reselected",
            "status": "accepted",
            "evidence": PREVIOUS_CK_CONSTRAINT_FAMILY,
            "assessment": (
                "The source-admissibility family is retained as a candidate-only "
                "reference, not treated as completed or reselected."
            ),
        },
        {
            "row_id": "bridge_family_selected_as_next_phi_relevant_family",
            "status": "accepted",
            "evidence": SELECTED_CK_CONSTRAINT_FAMILY,
            "assessment": (
                "Bridge-admissibility is selected as the next abstract "
                "phi-relevant C_k family."
            ),
        },
        {
            "row_id": "bridge_question_matches_next_seam_layer",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_QUESTION,
            "assessment": (
                "The selected family asks whether the phi route connects the "
                "scalar surface, QFT-GR source ladder, and master-action "
                "structure."
            ),
        },
        {
            "row_id": "bridge_candidate_shape_only_previewed",
            "status": "accepted",
            "evidence": BRIDGE_CANDIDATE_SHAPE_PREVIEW,
            "assessment": (
                "C_bridge^phi = 0 is recorded only as the next packet's "
                "candidate shape to test, not as a defined functional."
            ),
        },
        {
            "row_id": "route_alignment_sequence_recorded_for_next_packet",
            "status": "accepted",
            "evidence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
            "assessment": (
                "The selector records the route that the bridge packet should "
                "check for alignment."
            ),
        },
        {
            "row_id": "next_candidate_packet_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next live target is the phi bridge-admissibility C_k "
                "constraint candidate packet."
            ),
        },
        {
            "row_id": "no_candidate_functional_or_variation",
            "status": "accepted",
            "evidence": [
                "bridge_candidate_functional_defined=false",
                "ck_variation_executed=false",
            ],
            "assessment": (
                "The selector defines no bridge functional and executes no C_k "
                "variation."
            ),
        },
        {
            "row_id": "no_generation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "phi_generated_by_ck_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The selector preserves the nonpromotion boundary."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_relevant_ck_constraint_family_selection_after_source_admissibility",
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


def build_phi_relevant_ck_constraint_family_selection_after_source_admissibility(
    *,
    source_rule_closeout_path: Path = SOURCE_RULE_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    source_closeout = _read_json(source_rule_closeout_path)
    selection_criteria = _selection_criteria(source_closeout)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            source_closeout.get("schema_id") == SOURCE_RULE_CLOSEOUT_SCHEMA_ID
            and source_closeout.get("packet_id") == SOURCE_RULE_CLOSEOUT_PACKET_ID
            and source_closeout.get("outcome_id") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and source_closeout.get("closeout_result") == SOURCE_RULE_CLOSEOUT_RESULT
            and source_closeout.get("selected_next_target") == CONSUMED_TARGET
            and source_closeout.get("accepted") is True
        ),
        "source_rule_candidate_preserved": (
            source_closeout.get("candidate_constraint_id") == SOURCE_CANDIDATE_CONSTRAINT_ID
            and source_closeout.get("candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and source_closeout.get("candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and source_closeout.get("admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and source_closeout.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and source_closeout.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and source_closeout.get("on_shell_implication_form")
            == ON_SHELL_IMPLICATION_FORM
        ),
        "source_closeout_boundary_preserved": (
            source_closeout.get("first_phi_relevant_ck_admissibility_rule_candidate_closed")
            is True
            and source_closeout.get("source_admissibility_family_closed_as_candidate_only")
            is True
            and source_closeout.get("source_admissibility_family_completed") is False
            and source_closeout.get("candidate_recorded_as_rule_only") is True
            and source_closeout.get("candidate_recorded_as_action_term") is False
        ),
        "bridge_selection_is_abstract_family_only": (
            SELECTED_CK_OPTION_CLASS == "bridge_admissibility_constraint"
            and SELECTED_CK_CONSTRAINT_FAMILY
            == "phi_bridge_admissibility_constraint_family"
            and NEXT_TARGET
            == "prepare_phi_bridge_admissibility_ck_constraint_candidate_packet"
        ),
        "no_source_shortcut_claims": all(
            source_closeout.get(key) is False
            for key in [
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
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_rule_closeout_result": SOURCE_RULE_CLOSEOUT_RESULT,
        "source_selected_ck_option_class": PREVIOUS_CK_OPTION_CLASS,
        "source_selected_ck_constraint_family": PREVIOUS_CK_CONSTRAINT_FAMILY,
        "source_family_status": PREVIOUS_FAMILY_STATUS,
        "source_admissibility_question": SOURCE_ADMISSIBILITY_QUESTION,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source_on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "source_residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "source_on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "source_first_rule_classification": FIRST_RULE_CLASSIFICATION,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "selected_family_selection_status": SELECTED_FAMILY_SELECTION_STATUS,
        "bridge_admissibility_question": BRIDGE_ADMISSIBILITY_QUESTION,
        "bridge_candidate_shape_preview": BRIDGE_CANDIDATE_SHAPE_PREVIEW,
        "bridge_candidate_plain_meaning": BRIDGE_CANDIDATE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_count": len(BRIDGE_ROUTE_ALIGNMENT_SEQUENCE),
        "candidate_family_options": _candidate_family_options(),
        "candidate_family_option_count": 2,
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_target_prepared": True,
        "selector_target_accepted": True,
        "selection_executed": True,
        "bridge_admissibility_family_selected": True,
        "bridge_admissibility_recommended_only": False,
        "bridge_admissibility_candidate_packet_authorized": True,
        "bridge_admissibility_candidate_packet_prepared": False,
        "bridge_candidate_shape_preview_recorded": True,
        "bridge_candidate_functional_defined": False,
        "bridge_candidate_functional_selected": False,
        "bridge_candidate_rule_proved": False,
        "bridge_route_alignment_sequence_recorded": True,
        "bridge_route_alignment_verified": False,
        "source_admissibility_family_reselected": False,
        "source_admissibility_family_completed": False,
        "source_admissibility_family_closed_as_candidate_only": True,
        "source_rule_candidate_retained_as_context": True,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "candidate_action_insertion_executed": False,
        "ck_action_embedding_claimed": False,
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
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
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
            "Level 3 selector; selects the phi bridge-admissibility C_k family "
            "after source-admissibility rule closeout without defining a "
            "candidate functional, executing variation, or promoting the "
            "master action"
        ),
        "claim_ceiling": (
            "abstract phi-relevant C_k family selection only no bridge "
            "functional no bridge proof no C_k variation no phi generation no "
            "derived potential no new conservation proof no source "
            "admissibility proof no QFT-GR closure no semiclassical coupling no "
            "canonical master-action promotion"
        ),
        "mathematical_statement": (
            "The selector retains the closed source-admissibility rule "
            "candidate C_source^nu[g, phi] = 0 as context and selects "
            "phi_bridge_admissibility_constraint_family as the next abstract "
            "C_k family to test. The next packet may attempt a candidate shaped "
            "like C_bridge^phi = 0 for route alignment, but no such functional "
            "is defined here."
        ),
        "non_claim_boundary": (
            "This selector only chooses the phi bridge-admissibility C_k family "
            "as the next abstract family after the source-admissibility rule "
            "closeout. It does not define C_bridge^phi, does not prove bridge "
            "admissibility, does not verify the route alignment sequence, does "
            "not select a fully concrete C_k functional, does not embed a "
            "constraint into the action, does not select a multiplier or "
            "boundary policy, does not execute C_k variation, does not generate "
            "phi, does not derive V(phi), does not prove new conservation or "
            "source admissibility, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, does "
            "not claim empirical validation, and does not authorize public "
            "readiness."
        ),
        "critical_gate_fail_conditions": [
            "claim bridge-admissibility is proved",
            "define C_bridge^phi as a concrete functional in this selector",
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
            "ToeFormal.Derivation.PhiRelevantCKConstraintFamilySelectionAfterSourceAdmissibility",
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
            "source_rule_closeout_file": _ptr(source_rule_closeout_path),
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
            "Build the phi-relevant C_k family selector after source-admissibility."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    selection = build_phi_relevant_ck_constraint_family_selection_after_source_admissibility(
        captured_at_utc=args.captured_at_utc
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
