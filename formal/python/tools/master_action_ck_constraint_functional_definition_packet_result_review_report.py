from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_constraint_functional_definition_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    DEFAULT_OUT as CK_DEFINITION_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OPTION_CLASS_COUNT,
    OUTCOME_ID as CK_DEFINITION_PACKET_OUTCOME,
    PACKET_ID as CK_DEFINITION_PACKET_ID,
    PACKET_RESULT as CK_DEFINITION_PACKET_RESULT,
    PHI_RELEVANT_RECOMMENDED_CLASSES,
    SCHEMA_ID as CK_DEFINITION_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_RESULT_REVIEW_ACCEPTS_"
    "OPTIONS_INDEX_NO_SELECTION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "master_action_ck_constraint_functional_definition_result_review_accepts_"
    "options_index_no_selection_or_promotion"
)
NEXT_TARGET = "select_master_action_ck_constraint_family_for_phi_route"
NEXT_TARGET_KIND = "master_action_ck_constraint_family_selector_for_phi_route"
POST_SELECTION_RECOMMENDED_TARGET = (
    "prepare_phi_source_admissibility_ck_constraint_candidate_packet"
)
RECOMMENDED_SELECTOR_PRIORITY = "source_admissibility_constraint"
ALTERNATE_SELECTOR_PRIORITY = "bridge_admissibility_constraint"
SELECTOR_CANDIDATE_SET = [
    RECOMMENDED_SELECTOR_PRIORITY,
    ALTERNATE_SELECTOR_PRIORITY,
]
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCKConstraintFunctionalDefinitionPacketResultReview.lean"
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
            "row_id": "seven_ck_option_classes_indexed",
            "status": "accepted",
            "evidence": packet.get("indexed_constraint_ids"),
            "assessment": "The definition packet indexes exactly seven C_k option classes.",
        },
        {
            "row_id": "source_admissibility_phi_relevant_future_candidate_only",
            "status": "accepted",
            "evidence": "source_admissibility_constraint",
            "assessment": (
                "Source-admissibility is phi-relevant but remains a future "
                "selector candidate, not a selected C_k family."
            ),
        },
        {
            "row_id": "bridge_admissibility_phi_relevant_future_candidate_only",
            "status": "accepted",
            "evidence": "bridge_admissibility_constraint",
            "assessment": (
                "Bridge-admissibility is phi-relevant but remains a future "
                "selector candidate, not a selected C_k family."
            ),
        },
        {
            "row_id": "no_concrete_ck_family_selected",
            "status": "accepted",
            "evidence": "ck_constraint_functional_family_selected=false",
            "assessment": "The packet selects no concrete C_k functional family.",
        },
        {
            "row_id": "no_ck_variation_executed",
            "status": "accepted",
            "evidence": "ck_variation_executed=false",
            "assessment": "The packet records variation slots but executes no C_k variation.",
        },
        {
            "row_id": "no_phi_generation_theorem_claimed",
            "status": "accepted",
            "evidence": "native_generation_theorem_claimed=false",
            "assessment": "No theorem says C_k or the ToE generates phi.",
        },
        {
            "row_id": "no_v_phi_derivation_claimed",
            "status": "accepted",
            "evidence": "potential_derived=false",
            "assessment": "V(phi) remains selected/non-derived.",
        },
        {
            "row_id": "no_source_admissibility_or_conservation_claimed",
            "status": "accepted",
            "evidence": [
                "source_admissibility_claimed=false",
                "source_conservation_claimed=false",
            ],
            "assessment": (
                "No source admissibility or conservation result is newly "
                "proved by the C_k option index."
            ),
        },
        {
            "row_id": "no_qft_gr_closure_or_master_action_promotion_claimed",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "The review preserves no QFT-GR closure and no master-action promotion.",
        },
        {
            "row_id": "selector_next_target_selected_not_derivation",
            "status": "accepted",
            "evidence": [NEXT_TARGET, POST_SELECTION_RECOMMENDED_TARGET],
            "assessment": (
                "The next step is a selector for the phi-relevant C_k family, "
                "with source-admissibility prioritized for a later candidate packet."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "master_action_ck_constraint_functional_definition_packet_result_review"
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


def build_master_action_ck_constraint_functional_definition_packet_result_review(
    *,
    ck_definition_packet_path: Path = CK_DEFINITION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(ck_definition_packet_path)
    criteria = _review_criteria(packet)
    indexed_ids = set(packet.get("indexed_constraint_ids", []))
    acceptance_criteria = {
        "consumes_expected_review_target": (
            packet.get("schema_id") == CK_DEFINITION_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CK_DEFINITION_PACKET_ID
            and packet.get("outcome_id") == CK_DEFINITION_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "seven_option_classes_indexed": (
            packet.get("option_class_count") == OPTION_CLASS_COUNT
            and len(indexed_ids) == OPTION_CLASS_COUNT
        ),
        "source_and_bridge_future_candidates_only": (
            packet.get("phi_relevant_recommended_classes")
            == PHI_RELEVANT_RECOMMENDED_CLASSES
            and set(PHI_RELEVANT_RECOMMENDED_CLASSES) == set(SELECTOR_CANDIDATE_SET)
            and packet.get("ck_phi_relevant_constraint_class_selected") is False
        ),
        "no_concrete_ck_family_selected": (
            packet.get("ck_constraint_functional_family_selected") is False
            and packet.get("concrete_ck_functional_family_found") is False
        ),
        "no_ck_variation_executed": packet.get("options_indexed_no_selection") is True,
        "no_forbidden_claims": all(
            packet.get(key) is False
            for key in [
                "phi_generated_by_ck_claimed",
                "derived_v_phi_claimed",
                "potential_derived",
                "source_admissibility_claimed",
                "source_conservation_claimed",
                "qft_gr_closure_claimed",
                "master_action_promoted",
                "canonical_master_action_promoted",
                "native_generation_theorem_claimed",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_selection_recommended_target": POST_SELECTION_RECOMMENDED_TARGET,
        "ck_definition_packet_outcome": CK_DEFINITION_PACKET_OUTCOME,
        "ck_definition_packet_result": CK_DEFINITION_PACKET_RESULT,
        "option_class_count": packet.get("option_class_count"),
        "indexed_constraint_ids": packet.get("indexed_constraint_ids"),
        "review_accepts_options_index": True,
        "seven_ck_option_classes_indexed": True,
        "source_admissibility_phi_relevant_future_candidate_only": True,
        "bridge_admissibility_phi_relevant_future_candidate_only": True,
        "source_or_bridge_admissibility_recommended_for_future_selection": True,
        "selector_candidate_set": SELECTOR_CANDIDATE_SET,
        "recommended_selector_priority": RECOMMENDED_SELECTOR_PRIORITY,
        "alternate_selector_priority": ALTERNATE_SELECTOR_PRIORITY,
        "concrete_ck_family_selected": False,
        "ck_constraint_functional_family_selected": False,
        "ck_phi_relevant_constraint_class_selected": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "selector_authorized": True,
        "derivation_authorized": False,
        "source_admissibility_candidate_prioritized": True,
        "bridge_admissibility_candidate_retained_as_alternate": True,
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": "CK_OPTIONS_INDEX_REVIEW_ACCEPTED_SELECTOR_ONLY",
        "mathematical_statement": (
            "The review accepts the C_k constraint-functional option index: "
            "seven legal option classes are recorded, source- and "
            "bridge-admissibility are phi-relevant future candidates only, no "
            "concrete C_k family is selected, and no C_k variation is executed."
        ),
        "non_claim_boundary": (
            "This review accepts the C_k option index only. It does not select "
            "a concrete C_k family, execute C_k variation, claim phi generation, "
            "derive V(phi), prove source admissibility or conservation, close "
            "QFT-GR, authorize semiclassical coupling, promote the master "
            "action, claim empirical validation, or authorize public readiness. "
            "Source-admissibility is prioritized only as a selector recommendation. "
            "C_k remains inactive and undefined. V(phi) remains smooth "
            "bounded-below but not derived. C_k does not yet generate phi. "
            "There is no ToE-native matter derivation, no native-generation "
            "theorem, no source admissibility or conservation, no QFT-GR "
            "closure, and no canonical master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "select a concrete C_k family in this review",
            "execute C_k variation in this review",
            "claim phi generation by C_k",
            "claim V(phi) derived",
            "claim source admissibility or conservation newly proved",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "ck_content_fully_defined_claimed": False,
        "phi_generation_theorem_claimed": False,
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
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.MasterActionCKConstraintFunctionalDefinitionPacketResultReview",
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
            "prior_packet_file": _ptr(ck_definition_packet_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(review, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the master-action C_k constraint-functional definition "
            "packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = build_master_action_ck_constraint_functional_definition_packet_result_review(
        captured_at_utc=args.captured_at_utc
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
