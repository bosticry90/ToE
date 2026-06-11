from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_MR004_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_INVENTORY_TARGET,
    OUTCOME_ID as EXPECTED_MR004_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_MR004_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_MR004_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_MR004_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_MR_PACKET_PATH,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = DEFAULT_CAPTURED_AT_UTC
BLOCKER = "insufficient_assumptions_for_conservation"
ASSUMPTION_FAMILY = "mathematical_regularity_assumptions"
ACCEPTED_MR_ROWS = [
    "MR-ASSUMP-001-derivative_exchange_regular_boundary",
    "MR-ASSUMP-002-weak_strong_conservation_comparison_scope",
    "MR-ASSUMP-003-distributional_pairing_regular_domain",
    "MR-ASSUMP-004-limit_interchange_regularization_boundary",
]
COMPLETED_FAMILIES_AFTER_MR = [
    "operator_domain_assumptions",
    "renormalization_assumptions",
    "state_domain_assumptions",
    "mathematical_regularity_assumptions",
]
NONCLAIMS = {
    "limit_interchange_proved": False,
    "global_mathematical_regularity_discharged": False,
    "state_admissibility_claimed": False,
    "source_admissibility_claimed": False,
    "stress_energy_source_admissibility_claimed": False,
    "conservation_proved": False,
    "conservation_proof_object_constructed": False,
    "conservation_witness_constructed": False,
    "Bianchi_compatibility_claimed": False,
    "semiclassical_einstein_equation_derived": False,
    "qft_gr_seam_closed": False,
    "empirical_validation_claimed": False,
    "master_action_promoted": False,
    "release_assembly_authorized": False,
    "public_submission_authorized": False,
}

INVENTORY_SELECTION_SCHEMA_ID = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ROW_INVENTORY_SELECTION_20260610_v0"
)
INVENTORY_SELECTION_ID = "QFT_GR_MATHEMATICAL_REGULARITY_ROW_INVENTORY_SELECTION_v0"
INVENTORY_SELECTION_OUTCOME = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ROW_INVENTORY_SELECTION_CONFIRMS_"
    "EXHAUSTION_AFTER_MR_ASSUMP_004_AND_AUTHORIZES_CLOSEOUT_PREPARATION_ONLY"
)
INVENTORY_SELECTION_CLASSIFICATION = (
    "mathematical_regularity_inventory_exhausted_after_mr_assump_004"
)
INVENTORY_SELECTION_TARGET = (
    "execute_qft_gr_mathematical_regularity_row_inventory_selection"
)
MR_CLOSEOUT_PACKET_TARGET = (
    "prepare_qft_gr_mathematical_regularity_assumption_reduction_closeout_packet"
)
MR_CLOSEOUT_PACKET_REVIEW_TARGET = (
    "review_qft_gr_mathematical_regularity_assumption_reduction_closeout_packet_result"
)
POST_MR_WITNESS_PACKET_TARGET = (
    "prepare_qft_gr_post_mathematical_regularity_conserved_source_witness_"
    "reattempt_packet"
)
POST_MR_WITNESS_PACKET_REVIEW_TARGET = (
    "review_qft_gr_post_mathematical_regularity_conserved_source_witness_"
    "reattempt_packet_result"
)
POST_MR_WITNESS_ATTEMPT_TARGET = (
    "execute_qft_gr_post_mathematical_regularity_conserved_source_witness_"
    "reattempt"
)
POST_MR_WITNESS_ATTEMPT_REVIEW_TARGET = (
    "review_qft_gr_post_mathematical_regularity_conserved_source_witness_"
    "reattempt_result"
)
CLAIM_LADDER_TARGET = "prepare_toe_claim_ladder_artifact"
CORE_HYPOTHESIS_TARGET = "prepare_toe_core_hypothesis_artifact"
MINIMAL_MODEL_TARGET = "prepare_qft_gr_minimal_working_model_program_artifact"
COUNTERMODEL_TARGET = "prepare_qft_gr_countermodel_registry_artifact"
FALSIFIER_ADDENDUM_TARGET = "prepare_toe_falsifier_prediction_registry_addendum_artifact"
EXPERT_TRANSLATION_TARGET = "prepare_toe_expert_translation_layer_artifact"
FINAL_LIVE_TARGET = "select_next_post_toe_expert_translation_bounded_target"

INVENTORY_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MATHEMATICAL_REGULARITY_ROW_INVENTORY_SELECTION_20260610_v0.json"
)
MR_CLOSEOUT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260610_v0.json"
)
MR_CLOSEOUT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_20260610_v0.json"
)
WITNESS_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_20260610_v0.json"
)
WITNESS_PACKET_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_RESULT_REVIEW_20260610_v0.json"
)
WITNESS_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_20260610_v0.json"
)
WITNESS_ATTEMPT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_RESULT_REVIEW_20260610_v0.json"
)
MATURATION_INDEX_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_POST_WITNESS_MATURATION_INDEX_v0.json"
)
CLAIM_LADDER_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CLAIM_LADDER_v0.md"
CORE_HYPOTHESIS_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CORE_HYPOTHESIS_v0.md"
)
MINIMAL_MODEL_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "QFT_GR_MINIMAL_WORKING_MODEL_PROGRAM_v0.md"
)
COUNTERMODEL_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "QFT_GR_COUNTERMODEL_REGISTRY_v0.json"
)
FALSIFIER_ADDENDUM_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_FALSIFIER_AND_PREDICTION_REGISTRY_ADDENDUM_v0.md"
)
EXPERT_TRANSLATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_EXPERT_TRANSLATION_LAYER_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, Any]]) -> list[str]:
    return [str(row["target"]) for row in rows if row.get("decision") == "selected"]


def _candidate_reducible_rows(packet: dict[str, Any]) -> list[str]:
    rows = packet.get("candidate_reducible_assumptions", [])
    return [str(row.get("assumption_id")) for row in rows]


def _metadata(
    *,
    claim_level: str,
    claim_ceiling: str,
    scientific_role: str,
    repo_status: str,
    physical_significance: str,
    expert_legibility_gap: str = "requires expert translation layer before public posture",
    falsifier_link: str = "TOE_FALSIFIER_AND_PREDICTION_REGISTRY_ADDENDUM_v0",
    countermodel_link: str = "QFT_GR_COUNTERMODEL_REGISTRY_v0",
) -> dict[str, str | list[str]]:
    return {
        "claim_level": claim_level,
        "claim_ceiling": claim_ceiling,
        "scientific_role": scientific_role,
        "repo_status": repo_status,
        "promotion_blockers": [
            "no conservation proof object",
            "no conservation witness",
            "no source admissibility",
            "no Bianchi compatibility",
            "no semiclassical Einstein equation",
            "no QFT-GR seam closure",
            "no empirical validation",
            "no master-action promotion",
        ],
        "physical_significance": physical_significance,
        "expert_legibility_gap": expert_legibility_gap,
        "falsifier_link": falsifier_link,
        "countermodel_link": countermodel_link,
    }


def build_inventory_selection(
    *,
    mr004_result_review_path: Path = DEFAULT_MR004_RESULT_REVIEW_PATH,
    mr_packet_path: Path = DEFAULT_MR_PACKET_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(mr004_result_review_path)
    packet = _read_json(mr_packet_path)
    inventory = _candidate_reducible_rows(packet)
    accepted_row = "MR-ASSUMP-004-limit_interchange_regularization_boundary"
    if accepted_row not in inventory:
        classification = "mathematical_regularity_inventory_incoherent_requires_registry_repair"
        remaining_rows: list[str] = []
        selected_next_target = "prepare_qft_gr_mathematical_regularity_inventory_registry_repair_packet"
    else:
        idx = inventory.index(accepted_row)
        remaining_rows = inventory[idx + 1 :]
        if remaining_rows:
            classification = "next_mathematical_regularity_row_selected_from_inventory"
            row_slug = remaining_rows[0].split("-", 2)[-1].replace("_", "-")
            selected_next_target = f"prepare_qft_gr_{row_slug}_assumption_reduction_packet"
        else:
            classification = INVENTORY_SELECTION_CLASSIFICATION
            selected_next_target = MR_CLOSEOUT_PACKET_TARGET

    candidate_next_targets = [
        {
            "target": MR_CLOSEOUT_PACKET_TARGET,
            "decision": "selected" if not remaining_rows and classification == INVENTORY_SELECTION_CLASSIFICATION else "not_selected",
            "reason": "Selected only if repo-authoritative inventory has no row after MR-ASSUMP-004.",
        },
        {
            "target": "prepare_qft_gr_<next_row>_assumption_reduction_packet",
            "decision": "selected" if remaining_rows else "not_selected",
            "reason": "Selected only if the repo-authoritative inventory contains another MR row.",
        },
        {
            "target": "prepare_qft_gr_mathematical_regularity_inventory_registry_repair_packet",
            "decision": "selected" if classification.endswith("registry_repair") else "not_selected",
            "reason": "Selected only if MR-ASSUMP-004 is absent from the authoritative inventory.",
        },
    ]
    criteria = {
        "consumes_mr004_result_review": review.get("schema_id")
        == EXPECTED_MR004_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_MR004_RESULT_REVIEW_ID,
        "mr004_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_MR004_RESULT_REVIEW_OUTCOME,
        "mr004_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_MR004_RESULT_REVIEW_CLASSIFICATION,
        "mr004_selected_inventory_target": review.get("selected_next_target")
        == EXPECTED_CONSUMED_INVENTORY_TARGET,
        "reads_repo_authoritative_inventory": inventory == ACCEPTED_MR_ROWS,
        "does_not_invent_row": set(remaining_rows).issubset(set(inventory)),
        "selects_exactly_one_next_target": _selected_targets(candidate_next_targets)
        == [selected_next_target],
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": INVENTORY_SELECTION_SCHEMA_ID,
        "selection_id": INVENTORY_SELECTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_target": EXPECTED_CONSUMED_INVENTORY_TARGET,
        "consumes_mr004_result_review": EXPECTED_MR004_RESULT_REVIEW_ID,
        "consumes_mr004_result_review_pointer": _ptr(mr004_result_review_path),
        "source_mathematical_regularity_inventory": packet.get("packet_id"),
        "source_mathematical_regularity_inventory_pointer": _ptr(mr_packet_path),
        "outcome_id": INVENTORY_SELECTION_OUTCOME,
        "inventory_selection_classification": classification,
        "repo_authoritative_mathematical_regularity_row_inventory": inventory,
        "accepted_terminal_row": accepted_row,
        "remaining_mathematical_regularity_rows_after_mr_assump_004": remaining_rows,
        "inventory_exhausted_after_mr_assump_004": not remaining_rows
        and classification == INVENTORY_SELECTION_CLASSIFICATION,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": "mathematical_regularity_closeout_preparation"
        if selected_next_target == MR_CLOSEOUT_PACKET_TARGET
        else "conditional_inventory_followup",
        "candidate_next_targets": candidate_next_targets,
        "selection_count": 1,
        "blocker": BLOCKER,
        "selected_assumption_family": ASSUMPTION_FAMILY,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def build_mr_closeout_packet(
    *, inventory_path: Path = INVENTORY_SELECTION_PATH, captured_at_utc: str = CAPTURED_AT_UTC
) -> dict[str, Any]:
    inventory = _read_json(inventory_path)
    criteria = {
        "consumes_inventory_selection": inventory.get("schema_id")
        == INVENTORY_SELECTION_SCHEMA_ID,
        "inventory_exhausted": inventory.get("inventory_exhausted_after_mr_assump_004")
        is True,
        "inventory_selected_closeout": inventory.get("selected_next_target")
        == MR_CLOSEOUT_PACKET_TARGET,
        "all_mr_rows_present": inventory.get(
            "repo_authoritative_mathematical_regularity_row_inventory"
        )
        == ACCEPTED_MR_ROWS,
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260610_v0",
        "packet_id": "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_target": MR_CLOSEOUT_PACKET_TARGET,
        "consumes_inventory_selection": INVENTORY_SELECTION_ID,
        "consumes_inventory_selection_pointer": _ptr(inventory_path),
        "outcome_id": "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE",
        "closeout_classification": "qft_gr_mathematical_regularity_assumption_reduction_closeout_packet_prepared_no_witness_or_seam_closure",
        "closed_assumption_family_candidate": ASSUMPTION_FAMILY,
        "accepted_mathematical_regularity_assumption_rows": ACCEPTED_MR_ROWS,
        "accepted_mathematical_regularity_assumption_row_count": len(ACCEPTED_MR_ROWS),
        "remaining_mathematical_regularity_assumption_rows": [],
        "completed_prior_assumption_families": [
            "operator_domain_assumptions",
            "renormalization_assumptions",
            "state_domain_assumptions",
        ],
        "completed_assumption_families_if_reviewed": COMPLETED_FAMILIES_AFTER_MR,
        "blocker": BLOCKER,
        "conservation_blocker_remains": True,
        "selected_next_target": MR_CLOSEOUT_PACKET_REVIEW_TARGET,
        "candidate_next_targets": [
            {
                "target": MR_CLOSEOUT_PACKET_REVIEW_TARGET,
                "decision": "selected",
                "reason": "Closeout preparation must be result-reviewed before witness pressure.",
            },
            {
                "target": POST_MR_WITNESS_PACKET_TARGET,
                "decision": "not_authorized_until_result_review",
                "reason": "Witness reattempt is downstream of closeout result review.",
            },
        ],
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def build_mr_closeout_review(
    *, packet_path: Path = MR_CLOSEOUT_PACKET_PATH, captured_at_utc: str = CAPTURED_AT_UTC
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    criteria = {
        "consumes_closeout_packet": packet.get("packet_id")
        == "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_v0",
        "packet_selected_review": packet.get("selected_next_target")
        == MR_CLOSEOUT_PACKET_REVIEW_TARGET,
        "all_four_mr_rows_accepted": packet.get(
            "accepted_mathematical_regularity_assumption_rows"
        )
        == ACCEPTED_MR_ROWS,
        "remaining_rows_empty": packet.get("remaining_mathematical_regularity_assumption_rows")
        == [],
        "preserves_blocker": packet.get("blocker") == BLOCKER,
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_20260610_v0",
        "review_id": "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": all(criteria.values()),
        "review_decision": "accept" if all(criteria.values()) else "reject",
        "consumed_target": MR_CLOSEOUT_PACKET_REVIEW_TARGET,
        "consumes_closeout_packet": packet.get("packet_id"),
        "consumes_closeout_packet_pointer": _ptr(packet_path),
        "outcome_id": "QFT_GR_MATHEMATICAL_REGULARITY_CLOSEOUT_RESULT_REVIEW_ACCEPTS_FAMILY_CLOSEOUT_AND_AUTHORIZES_POST_MR_WITNESS_REATTEMPT_PACKET_ONLY",
        "result_review_classification": "qft_gr_mathematical_regularity_closeout_result_review_accepts_family_closeout_and_authorizes_post_mr_witness_reattempt_packet_only",
        "closed_assumption_family": ASSUMPTION_FAMILY,
        "accepted_mathematical_regularity_assumption_rows": ACCEPTED_MR_ROWS,
        "accepted_mathematical_regularity_assumption_row_count": len(ACCEPTED_MR_ROWS),
        "remaining_mathematical_regularity_assumption_rows": [],
        "completed_assumption_families_for_this_lane": COMPLETED_FAMILIES_AFTER_MR,
        "blocker": BLOCKER,
        "conservation_blocker_remains": True,
        "selected_next_target": POST_MR_WITNESS_PACKET_TARGET,
        "candidate_next_targets": [
            {
                "target": POST_MR_WITNESS_PACKET_TARGET,
                "decision": "selected",
                "reason": "Family closeout must force witness pressure before any new assumption family.",
            },
            {
                "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
                "decision": "not_authorized_before_witness_reattempt",
                "reason": "Bianchi work remains downstream of witness pressure.",
            },
            {
                "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
                "decision": "not_authorized_before_witness_reattempt",
                "reason": "Physical source-admissibility work remains downstream of witness pressure.",
            },
        ],
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def build_witness_packet(
    *, closeout_review_path: Path = MR_CLOSEOUT_REVIEW_PATH, captured_at_utc: str = CAPTURED_AT_UTC
) -> dict[str, Any]:
    review = _read_json(closeout_review_path)
    criteria = {
        "consumes_mr_closeout_review": review.get("review_id")
        == "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "closeout_selected_witness_packet": review.get("selected_next_target")
        == POST_MR_WITNESS_PACKET_TARGET,
        "completed_four_families_available": review.get(
            "completed_assumption_families_for_this_lane"
        )
        == COMPLETED_FAMILIES_AFTER_MR,
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_20260610_v0",
        "packet_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_target": POST_MR_WITNESS_PACKET_TARGET,
        "consumes_mr_closeout_review": review.get("review_id"),
        "consumes_mr_closeout_review_pointer": _ptr(closeout_review_path),
        "outcome_id": "QFT_GR_POST_MR_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_PREPARED_WITH_NO_WITNESS_OR_SEAM_CLOSURE",
        "packet_classification": "qft_gr_post_mr_conserved_source_witness_reattempt_packet_prepared_no_witness_or_seam_closure",
        "witness_question": "Do the completed operator-domain, renormalization, state-domain, and mathematical-regularity reductions now support any bounded conserved/source-admissible QFT-GR source witness?",
        "completed_assumption_families_available": COMPLETED_FAMILIES_AFTER_MR,
        "allowed_outcomes": [
            "bounded_witness_constructed_pending_review",
            "bounded_witness_obstruction_identified_requires_next_family",
            "bounded_witness_inconclusive_requires_model_demonstration",
            "witness_route_invalid_requires_countermodel_or_scope_rewrite",
        ],
        "selected_next_target": POST_MR_WITNESS_PACKET_REVIEW_TARGET,
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def build_witness_packet_review(
    *, packet_path: Path = WITNESS_PACKET_PATH, captured_at_utc: str = CAPTURED_AT_UTC
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    criteria = {
        "consumes_witness_packet": packet.get("packet_id")
        == "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_v0",
        "packet_selected_review": packet.get("selected_next_target")
        == POST_MR_WITNESS_PACKET_REVIEW_TARGET,
        "allowed_outcomes_present": "bounded_witness_inconclusive_requires_model_demonstration"
        in packet.get("allowed_outcomes", []),
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_RESULT_REVIEW_20260610_v0",
        "review_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_RESULT_REVIEW_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": all(criteria.values()),
        "review_decision": "accept" if all(criteria.values()) else "reject",
        "consumed_target": POST_MR_WITNESS_PACKET_REVIEW_TARGET,
        "consumes_witness_packet": packet.get("packet_id"),
        "consumes_witness_packet_pointer": _ptr(packet_path),
        "outcome_id": "QFT_GR_POST_MR_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_ATTEMPT_ONLY",
        "result_review_classification": "qft_gr_post_mr_conserved_source_witness_reattempt_packet_result_review_accepts_packet_and_authorizes_bounded_attempt_only",
        "selected_next_target": POST_MR_WITNESS_ATTEMPT_TARGET,
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def build_witness_attempt(
    *,
    packet_review_path: Path = WITNESS_PACKET_REVIEW_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_review_path)
    criteria = {
        "consumes_packet_review": review.get("review_id")
        == "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_PACKET_RESULT_REVIEW_v0",
        "packet_review_selected_attempt": review.get("selected_next_target")
        == POST_MR_WITNESS_ATTEMPT_TARGET,
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_20260610_v0",
        "attempt_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_target": POST_MR_WITNESS_ATTEMPT_TARGET,
        "consumes_packet_review": review.get("review_id"),
        "consumes_packet_review_pointer": _ptr(packet_review_path),
        "outcome_id": "QFT_GR_POST_MR_CONSERVED_SOURCE_WITNESS_REATTEMPT_EXECUTED_INCONCLUSIVE_REQUIRES_MODEL_DEMONSTRATION",
        "result_classification": "bounded_witness_inconclusive_requires_model_demonstration",
        "attempt_question_answered": True,
        "bounded_witness_constructed": False,
        "bounded_witness_obstruction_identified_requires_next_family": False,
        "bounded_witness_inconclusive_requires_model_demonstration": True,
        "witness_route_invalid_requires_countermodel_or_scope_rewrite": False,
        "next_assumption_family_opened": False,
        "missing_condition_family_named": None,
        "reason": "The row-level reductions now define the witness pressure point, but the repo still lacks a minimal model demonstration showing that the candidate source can be carried across the seam under explicit assumptions.",
        "selected_next_target": POST_MR_WITNESS_ATTEMPT_REVIEW_TARGET,
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def build_witness_attempt_review(
    *,
    attempt_path: Path = WITNESS_ATTEMPT_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    criteria = {
        "consumes_witness_attempt": attempt.get("attempt_id")
        == "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_v0",
        "attempt_selected_review": attempt.get("selected_next_target")
        == POST_MR_WITNESS_ATTEMPT_REVIEW_TARGET,
        "classification_allowed": attempt.get("result_classification")
        == "bounded_witness_inconclusive_requires_model_demonstration",
        "does_not_open_next_assumption_family": attempt.get("next_assumption_family_opened")
        is False,
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_RESULT_REVIEW_20260610_v0",
        "review_id": "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_RESULT_REVIEW_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": all(criteria.values()),
        "review_decision": "accept" if all(criteria.values()) else "reject",
        "consumed_target": POST_MR_WITNESS_ATTEMPT_REVIEW_TARGET,
        "consumes_witness_attempt": attempt.get("attempt_id"),
        "consumes_witness_attempt_pointer": _ptr(attempt_path),
        "outcome_id": "QFT_GR_POST_MR_CONSERVED_SOURCE_WITNESS_REATTEMPT_RESULT_REVIEW_ACCEPTS_INCONCLUSIVE_MODEL_DEMONSTRATION_ROUTE",
        "result_review_classification": "qft_gr_post_mr_conserved_source_witness_reattempt_result_review_accepts_inconclusive_model_demonstration_route",
        "accepted_attempt_classification": attempt.get("result_classification"),
        "next_assumption_family_authorized": False,
        "maturation_artifacts_authorized_after_witness_review": True,
        "selected_next_target": CLAIM_LADDER_TARGET,
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def _metadata_block(meta: dict[str, Any]) -> str:
    lines = ["## Metadata"]
    for key in [
        "claim_level",
        "claim_ceiling",
        "scientific_role",
        "repo_status",
        "physical_significance",
        "expert_legibility_gap",
        "falsifier_link",
        "countermodel_link",
    ]:
        lines.append(f"- `{key}`: {meta[key]}")
    blockers = ", ".join(meta["promotion_blockers"])
    lines.append(f"- `promotion_blockers`: {blockers}")
    return "\n".join(lines)


def _claim_ladder_doc(meta: dict[str, Any]) -> str:
    return f"""# ToE Claim Ladder v0

{_metadata_block(meta)}

## Levels

- Level 0: Governance artifact.
- Level 1: Formal object under assumptions.
- Level 2: Bounded local reduction.
- Level 3: Toy-model demonstration.
- Level 4: Pillar recovery.
- Level 5: Seam admissibility.
- Level 6: Seam closure.
- Level 7: Empirical-facing prediction.
- Level 8: Empirical confirmation.
- Level 9: Mature physical theory.

## Current Placement

Current QFT-GR work remains Level 0-2. The next maturation target is Level 3,
but only after the post-mathematical-regularity witness reattempt has been
reviewed.
"""


def _core_hypothesis_doc(meta: dict[str, Any]) -> str:
    return f"""# ToE Core Hypothesis v0

{_metadata_block(meta)}

## Core Hypothesis

A true ToE is not merely a master equation. It is a master equation plus a
complete seam-admissibility theory.

Known physics may be different stable regimes of a deeper constrained system,
but unification requires proving that objects transported across seams satisfy
domain, regularity, admissibility, conservation, and compatibility conditions.

## Current Boundary

This artifact does not claim source admissibility, conservation, Bianchi
compatibility, semiclassical Einstein coupling, QFT-GR closure, empirical
validation, or master-action promotion.
"""


def _minimal_model_doc(meta: dict[str, Any]) -> str:
    return f"""# QFT-GR Minimal Working Model Program v0

{_metadata_block(meta)}

## Target Chain

```text
field object
-> state/expectation object
-> stress-energy-like object
-> regularized or renormalized candidate
-> distributional pairing domain
-> derivative/interchange conditions
-> weak conservation condition
-> source-admissibility candidate
```

## First Model

Use a free scalar-field stress-energy-like source candidate on a simplified
fixed curved or controlled background. The model may prove a bounded source
candidate or expose a precise obstruction.
"""


def _falsifier_doc(meta: dict[str, Any]) -> str:
    return f"""# ToE Falsifier And Prediction Registry Addendum v0

{_metadata_block(meta)}

## Seam-Centric Formal Falsifiers

- QFT-GR source admissibility falsifier: no toy-model source candidate under
  the accepted reductions implies the current route is insufficient.
- QFT-GR weak/strong conservation falsifier: inability to distinguish the
  conservation senses weakens MR-ASSUMP-002.
- QFT-GR derivative/limit interchange falsifier: pairability without derivative
  exchange blocks the conservation route.
- QM-STAT entropy semantics falsifier: residual-zero transport without semantic
  entropy closure remains insufficient.
- SR-COSMO local/global bridge falsifier: local regime transport without global
  semantic map remains insufficient.
"""


def _expert_translation_doc(meta: dict[str, Any]) -> str:
    return f"""# ToE Expert Translation Layer v0

{_metadata_block(meta)}

## Translation Table

| Internal term | Expert-facing analog |
| --- | --- |
| seam | compatibility condition, matching condition, bridge theorem |
| source admissibility | validity of stress-energy as a source in target geometry |
| regularity assumptions | differentiability, distributional pairing, limit-exchange, domain conditions |
| weak conservation | distributional or tested conservation condition |
| strong conservation | pointwise, operator-level, or identity-level conservation condition |
| semantic closure | interpretation-preserving map or model-theoretic bridge |
| witness | proof object or constructive bridge certificate |
| residual zero | local equation match, cancellation, or error residual vanishing |

Project-specific terms are not presented as standard terminology.
"""


def build_countermodel_registry() -> dict[str, Any]:
    meta = _metadata(
        claim_level="Level 2 registry preparing Level 3 discrimination",
        claim_ceiling="countermodel registration only",
        scientific_role="discriminate fake, partial, and candidate bridges",
        repo_status="post-witness maturation artifact",
        physical_significance="shows that local success does not imply seam admissibility",
    )
    return {
        "registry_id": "QFT_GR_COUNTERMODEL_REGISTRY_v0",
        "metadata": meta,
        "countermodels": [
            {
                "case_id": "QFT_GR_COUNTERMODEL_001_RESIDUAL_ZERO_NOT_ADMISSIBLE",
                "what_succeeds": "residual equality",
                "what_fails": "target-theory source admissibility",
                "false_claim_blocked": "residual_zero_implies_source_admissible",
                "status": "registered_not_executed",
            },
            {
                "case_id": "QFT_GR_COUNTERMODEL_002_EXPECTATION_NOT_CONSERVED",
                "what_succeeds": "expectation object exists",
                "what_fails": "covariant conservation",
                "false_claim_blocked": "expectation_exists_implies_conserved_source",
                "status": "registered_not_executed",
            },
            {
                "case_id": "QFT_GR_COUNTERMODEL_003_PAIRING_WITHOUT_DERIVATIVE_EXCHANGE",
                "what_succeeds": "distributional pairing exists",
                "what_fails": "derivative exchange",
                "false_claim_blocked": "pairing_domain_implies_conservation_route",
                "status": "registered_not_executed",
            },
        ],
        "promotion_allowed": False,
    }


def build_maturation_index(
    *,
    witness_review_path: Path = WITNESS_ATTEMPT_REVIEW_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(witness_review_path)
    artifact_order = [
        _ptr(CLAIM_LADDER_PATH),
        _ptr(CORE_HYPOTHESIS_PATH),
        _ptr(MINIMAL_MODEL_PATH),
        _ptr(COUNTERMODEL_REGISTRY_PATH),
        _ptr(FALSIFIER_ADDENDUM_PATH),
        _ptr(EXPERT_TRANSLATION_PATH),
    ]
    criteria = {
        "consumes_witness_result_review": review.get("review_id")
        == "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_RESULT_REVIEW_v0",
        "witness_review_authorizes_maturation": review.get(
            "maturation_artifacts_authorized_after_witness_review"
        )
        is True,
        "artifact_order_preserved": artifact_order
        == [
            "formal/docs/paper/TOE_CLAIM_LADDER_v0.md",
            "formal/docs/paper/TOE_CORE_HYPOTHESIS_v0.md",
            "formal/docs/paper/QFT_GR_MINIMAL_WORKING_MODEL_PROGRAM_v0.md",
            "formal/docs/paper/QFT_GR_COUNTERMODEL_REGISTRY_v0.json",
            "formal/docs/paper/TOE_FALSIFIER_AND_PREDICTION_REGISTRY_ADDENDUM_v0.md",
            "formal/docs/paper/TOE_EXPERT_TRANSLATION_LAYER_v0.md",
        ],
    }
    return {
        "schema_id": "TOE_POST_WITNESS_MATURATION_INDEX_20260610_v0",
        "index_id": "TOE_POST_WITNESS_MATURATION_INDEX_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumes_witness_result_review": review.get("review_id"),
        "consumes_witness_result_review_pointer": _ptr(witness_review_path),
        "outcome_id": "TOE_POST_WITNESS_MATURATION_ARTIFACTS_PREPARED_AFTER_WITNESS_PRESSURE_WITH_NO_PROMOTION",
        "artifact_order": artifact_order,
        "selected_next_target": FINAL_LIVE_TARGET,
        "selection_count": 1,
        "acceptance_criteria": criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def write_all(*, captured_at_utc: str = CAPTURED_AT_UTC) -> dict[str, Any]:
    outputs: dict[str, Any] = {}

    def write_payload(path: Path, payload: dict[str, Any]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        outputs[_ptr(path)] = payload

    write_payload(
        INVENTORY_SELECTION_PATH,
        build_inventory_selection(captured_at_utc=captured_at_utc),
    )
    write_payload(
        MR_CLOSEOUT_PACKET_PATH,
        build_mr_closeout_packet(captured_at_utc=captured_at_utc),
    )
    write_payload(
        MR_CLOSEOUT_REVIEW_PATH,
        build_mr_closeout_review(captured_at_utc=captured_at_utc),
    )
    write_payload(WITNESS_PACKET_PATH, build_witness_packet(captured_at_utc=captured_at_utc))
    write_payload(
        WITNESS_PACKET_REVIEW_PATH,
        build_witness_packet_review(captured_at_utc=captured_at_utc),
    )
    write_payload(WITNESS_ATTEMPT_PATH, build_witness_attempt(captured_at_utc=captured_at_utc))
    write_payload(
        WITNESS_ATTEMPT_REVIEW_PATH,
        build_witness_attempt_review(captured_at_utc=captured_at_utc),
    )

    claim_meta = _metadata(
        claim_level="Level 0-2 classifier",
        claim_ceiling="claim classification only",
        scientific_role="prevent local reductions from being promoted to closure",
        repo_status="post-witness maturation artifact",
        physical_significance="keeps toy-model progress distinct from seam closure",
    )
    core_meta = _metadata(
        claim_level="Level 0-2 thesis compression",
        claim_ceiling="hypothesis statement only",
        scientific_role="compress seam-admissibility thesis",
        repo_status="post-witness maturation artifact",
        physical_significance="states why seam rules, not a standalone equation, carry unifying content",
    )
    model_meta = _metadata(
        claim_level="Level 3 program target",
        claim_ceiling="toy-model program only",
        scientific_role="define positive model demonstration path",
        repo_status="post-witness maturation artifact",
        physical_significance="creates the first small source-carrying test case",
    )
    falsifier_meta = _metadata(
        claim_level="Level 2-3 falsifier design",
        claim_ceiling="test-design registration only",
        scientific_role="register formal and toy-model falsifiers",
        repo_status="post-witness maturation artifact",
        physical_significance="gives seam-admissibility claims failure conditions",
    )
    translation_meta = _metadata(
        claim_level="Level 0 translation layer",
        claim_ceiling="terminology mapping only",
        scientific_role="make internal vocabulary expert-legible",
        repo_status="post-witness maturation artifact",
        physical_significance="maps project-specific labels to physics and mathematics analogs",
        expert_legibility_gap="none for listed terms; deeper literature mapping remains future work",
    )

    docs = {
        CLAIM_LADDER_PATH: _claim_ladder_doc(claim_meta),
        CORE_HYPOTHESIS_PATH: _core_hypothesis_doc(core_meta),
        MINIMAL_MODEL_PATH: _minimal_model_doc(model_meta),
        FALSIFIER_ADDENDUM_PATH: _falsifier_doc(falsifier_meta),
        EXPERT_TRANSLATION_PATH: _expert_translation_doc(translation_meta),
    }
    for path, text in docs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        outputs[_ptr(path)] = {"text_length": len(text)}

    COUNTERMODEL_REGISTRY_PATH.write_text(
        json.dumps(build_countermodel_registry(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    outputs[_ptr(COUNTERMODEL_REGISTRY_PATH)] = build_countermodel_registry()

    MATURATION_INDEX_PATH.write_text(
        json.dumps(build_maturation_index(captured_at_utc=captured_at_utc), indent=2, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )
    outputs[_ptr(MATURATION_INDEX_PATH)] = build_maturation_index(
        captured_at_utc=captured_at_utc
    )
    return outputs


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate post-MR-ASSUMP-004 governed maturation artifacts."
    )
    parser.add_argument("--captured-at-utc", default=CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    outputs = write_all(captured_at_utc=str(ns.captured_at_utc))
    print(
        "qft_gr_post_mr_assump004_governed_maturation_reports: "
        f"wrote={len(outputs)} final_next={FINAL_LIVE_TARGET}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
