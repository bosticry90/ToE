from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_constraint_functional_definition_packet_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALTERNATE_SELECTOR_PRIORITY,
    DEFAULT_OUT as CK_DEFINITION_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CK_DEFINITION_REVIEW_OUTCOME,
    PACKET_ID as CK_DEFINITION_REVIEW_PACKET_ID,
    POST_SELECTION_RECOMMENDED_TARGET as NEXT_TARGET,
    RECOMMENDED_SELECTOR_PRIORITY,
    REVIEW_RESULT as CK_DEFINITION_REVIEW_RESULT,
    SCHEMA_ID as CK_DEFINITION_REVIEW_SCHEMA_ID,
    SELECTOR_CANDIDATE_SET,
)
from formal.python.tools.qft_gr_provisional_scalar_classical_source_route_witness_closeout_report import (
    DEFAULT_OUT as SCALAR_WITNESS_CLOSEOUT_PATH,
    OUTCOME_ID as SCALAR_WITNESS_CLOSEOUT_OUTCOME,
    POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION,
    PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
    SCHEMA_ID as SCALAR_WITNESS_CLOSEOUT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_FOR_PHI_ROUTE_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_FOR_PHI_ROUTE_v0"
SELECTION_RESULT = (
    "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_SELECTS_PHI_SOURCE_"
    "ADMISSIBILITY_CONSTRAINT_FAMILY_NO_CK_FUNCTIONAL_EXECUTION_OR_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "master_action_ck_constraint_family_selection_selects_phi_source_"
    "admissibility_family_no_functional_execution_or_promotion"
)
NEXT_TARGET_KIND = "phi_source_admissibility_ck_constraint_candidate_packet_preparation"
SELECTED_CK_OPTION_CLASS = RECOMMENDED_SELECTOR_PRIORITY
SELECTED_CK_CONSTRAINT_FAMILY = "phi_source_admissibility_constraint_family"
DEFERRED_ALTERNATE_CK_OPTION_CLASS = ALTERNATE_SELECTOR_PRIORITY
SELECTED_FAMILY_SELECTION_STATUS = "selected_as_abstract_option_family"
DEFERRED_FAMILY_SELECTION_STATUS = "deferred_not_rejected"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

SOURCE_ROUTE_REFERENCE_PATTERN = [
    "action-derived stress-energy",
    "on-shell conservation",
    "Bianchi compatibility",
    "local source admissibility",
    "classical Einstein-scalar coupling",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_FOR_PHI_ROUTE_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKConstraintFamilySelectionForPhiRoute.lean"
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
            "constraint_option_class": SELECTED_CK_OPTION_CLASS,
            "constraint_family_id": SELECTED_CK_CONSTRAINT_FAMILY,
            "selection_status": SELECTED_FAMILY_SELECTION_STATUS,
            "phi_relevance": "highest",
            "selection_reason": (
                "The scalar witness already supplies an action-derived, "
                "on-shell conserved, Bianchi-compatible, locally admissible "
                "classical source route, so source-admissibility has a concrete "
                "reference pattern for the next candidate packet."
            ),
            "candidate_packet_target": NEXT_TARGET,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
        {
            "constraint_option_class": DEFERRED_ALTERNATE_CK_OPTION_CLASS,
            "constraint_family_id": "phi_bridge_admissibility_constraint_family",
            "selection_status": DEFERRED_FAMILY_SELECTION_STATUS,
            "phi_relevance": "high",
            "selection_reason": (
                "Bridge-admissibility remains important but is broader and more "
                "abstract than the source-admissibility family for the immediate "
                "phi route."
            ),
            "candidate_packet_target": "prepare_phi_bridge_admissibility_ck_constraint_candidate_packet",
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "physical_law_claimed": False,
        },
    ]


def _selection_criteria(
    *,
    review: dict[str, Any],
    scalar_witness: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_current_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The packet consumes the active C_k family selector target.",
        },
        {
            "row_id": "ck_option_index_review_accepted",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": "The selector starts from an accepted option index.",
        },
        {
            "row_id": "candidate_set_is_source_or_bridge",
            "status": "accepted",
            "evidence": SELECTOR_CANDIDATE_SET,
            "assessment": "Only source- and bridge-admissibility are considered for the phi selector.",
        },
        {
            "row_id": "scalar_witness_supplies_source_reference_pattern",
            "status": "accepted",
            "evidence": [
                scalar_witness.get("positive_local_classical_source_witness_classification"),
                scalar_witness.get("provisional_scalar_source_admissibility_result"),
            ],
            "assessment": (
                "The imported scalar witness supplies the source-route pattern "
                "that a future C_source^phi candidate can attempt to encode."
            ),
        },
        {
            "row_id": "source_admissibility_selected_as_nearest_phi_family",
            "status": "accepted",
            "evidence": SELECTED_CK_OPTION_CLASS,
            "assessment": "Source-admissibility is the nearest family for the next phi candidate packet.",
        },
        {
            "row_id": "bridge_admissibility_deferred_not_rejected",
            "status": "accepted",
            "evidence": DEFERRED_ALTERNATE_CK_OPTION_CLASS,
            "assessment": "Bridge-admissibility is deferred, not rejected.",
        },
        {
            "row_id": "selection_is_abstract_family_not_concrete_functional",
            "status": "accepted",
            "evidence": "concrete_ck_functional_selected=false",
            "assessment": "No mathematical C_k functional formula is selected in this packet.",
        },
        {
            "row_id": "next_candidate_packet_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next packet may attempt a phi source-admissibility C_k candidate.",
        },
        {
            "row_id": "no_ck_variation_or_phi_generation",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "phi_generated_by_ck_claimed=false",
            ],
            "assessment": "The selector executes no variation and makes no phi-generation claim.",
        },
        {
            "row_id": "no_closure_promotion_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "The selector preserves the nonpromotion boundary.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_ck_constraint_family_selection_for_phi_route",
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


def build_master_action_ck_constraint_family_selection_for_phi_route(
    *,
    ck_definition_review_path: Path = CK_DEFINITION_REVIEW_PATH,
    scalar_witness_closeout_path: Path = SCALAR_WITNESS_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(ck_definition_review_path)
    scalar_witness = _read_json(scalar_witness_closeout_path)
    family_options = _candidate_family_options()
    criteria = _selection_criteria(review=review, scalar_witness=scalar_witness)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            review.get("schema_id") == CK_DEFINITION_REVIEW_SCHEMA_ID
            and review.get("packet_id") == CK_DEFINITION_REVIEW_PACKET_ID
            and review.get("outcome_id") == CK_DEFINITION_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "review_result_accepts_options_index": (
            review.get("review_result") == CK_DEFINITION_REVIEW_RESULT
            and review.get("review_accepts_options_index") is True
            and review.get("selector_candidate_set") == SELECTOR_CANDIDATE_SET
        ),
        "scalar_witness_reference_available": (
            scalar_witness.get("schema_id") == SCALAR_WITNESS_CLOSEOUT_SCHEMA_ID
            and scalar_witness.get("outcome_id") == SCALAR_WITNESS_CLOSEOUT_OUTCOME
            and scalar_witness.get("accepted") is True
            and scalar_witness.get("positive_local_classical_source_witness_closed")
            is True
        ),
        "source_admissibility_selected": (
            SELECTED_CK_OPTION_CLASS == "source_admissibility_constraint"
            and SELECTED_CK_CONSTRAINT_FAMILY
            == "phi_source_admissibility_constraint_family"
        ),
        "bridge_admissibility_deferred": (
            DEFERRED_ALTERNATE_CK_OPTION_CLASS == "bridge_admissibility_constraint"
        ),
        "selected_family_is_not_concrete_functional": True,
        "no_ck_variation_executed": True,
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in criteria
        ),
        "next_candidate_packet_selected": (
            NEXT_TARGET == "prepare_phi_source_admissibility_ck_constraint_candidate_packet"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_FOR_PHI_ROUTE"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_FOR_PHI_ROUTE",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "ck_definition_review_result": CK_DEFINITION_REVIEW_RESULT,
        "scalar_witness_closeout_outcome": SCALAR_WITNESS_CLOSEOUT_OUTCOME,
        "scalar_witness_classification": (
            POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION
        ),
        "scalar_source_admissibility_reference_result": (
            PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
        ),
        "source_route_reference_pattern": SOURCE_ROUTE_REFERENCE_PATTERN,
        "selector_candidate_set": SELECTOR_CANDIDATE_SET,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "selected_family_selection_status": SELECTED_FAMILY_SELECTION_STATUS,
        "deferred_alternate_ck_option_class": DEFERRED_ALTERNATE_CK_OPTION_CLASS,
        "deferred_family_selection_status": DEFERRED_FAMILY_SELECTION_STATUS,
        "candidate_family_options": family_options,
        "candidate_family_option_count": len(family_options),
        "candidate_family_options_selected_count": sum(
            1
            for row in family_options
            if row["selection_status"] == SELECTED_FAMILY_SELECTION_STATUS
        ),
        "candidate_family_options_deferred_count": sum(
            1
            for row in family_options
            if row["selection_status"] == DEFERRED_FAMILY_SELECTION_STATUS
        ),
        "ck_constraint_family_selection_executed": True,
        "source_admissibility_constraint_family_selected": True,
        "bridge_admissibility_constraint_family_deferred": True,
        "selected_family_is_abstract_option_class": True,
        "selected_family_has_reference_pattern": True,
        "candidate_packet_authorized": accepted,
        "candidate_packet_target": selected_next_target,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_selected": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "ck_family_claimed_as_physical_law": False,
        "phi_generated_by_ck_claimed": False,
        "derived_v_phi_claimed": False,
        "v_phi_derivation_claimed": False,
        "potential_derived": False,
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
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "selection_criteria": criteria,
        "selection_criteria_count": len(criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": "CK_FAMILY_SELECTOR_SELECTED_ABSTRACT_SOURCE_ADMISSIBILITY_ONLY",
        "mathematical_statement": (
            "The selector chooses the source-admissibility C_k family as the "
            "next abstract family for the phi route because the imported scalar "
            "witness supplies an action-derived, on-shell conserved, "
            "Bianchi-compatible, locally admissible classical source pattern. "
            "The selector defines no concrete C_k functional and executes no "
            "C_k variation."
        ),
        "non_claim_boundary": (
            "This selector selects only the abstract source-admissibility "
            "constraint family for the next phi C_k candidate packet. It does "
            "not select or define a concrete C_k functional, execute C_k "
            "variation, claim phi generation, derive V(phi), prove source "
            "admissibility or conservation, close QFT-GR, authorize "
            "semiclassical coupling, promote the master action, claim empirical "
            "validation, or authorize public readiness. C_k remains inactive "
            "and undefined at the functional level. V(phi) remains smooth "
            "bounded-below but not derived. C_k does not yet generate phi. "
            "There is no ToE-native matter derivation, no native-generation "
            "theorem, no source admissibility or conservation, no QFT-GR "
            "closure, and no canonical master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "claim a concrete C_k functional is selected",
            "execute C_k variation",
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
            "ToeFormal.Derivation.MasterActionCKConstraintFamilySelectionForPhiRoute",
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
            "ck_definition_review_file": _ptr(ck_definition_review_path),
            "scalar_witness_closeout_file": _ptr(scalar_witness_closeout_path),
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
        description="Build the master-action C_k family selector for the phi route."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    selection = build_master_action_ck_constraint_family_selection_for_phi_route(
        captured_at_utc=args.captured_at_utc
    )
    path = write_selection(selection, args.out)
    print(
        json.dumps(
            {
                "accepted": selection["accepted"],
                "out": _ptr(path),
                "outcome_id": selection["outcome_id"],
                "selected_ck_constraint_family": selection[
                    "selected_ck_constraint_family"
                ],
                "selected_next_target": selection["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
