from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-07-02T00:00:00Z"

LEAN_STATUS_WORDING = (
    "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION; "
    "scoped Lean targets = PASSED_SERIAL_RERUN"
)
LEAN_STATUS_WORDING_LINES = [
    "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
    "scoped Lean targets = PASSED_SERIAL_RERUN",
]
FULL_TOEFORMAL_AGGREGATE_STATUS = "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
SCOPED_LEAN_TARGETS_STATUS = "PASSED_SERIAL_RERUN"

LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL = (
    "local phi source/bridge/transport theorem-linkage triad"
)
LOCAL_PHI_TRIAD_EQUATIONS = [
    "C_source^phi = 0",
    "C_bridge^phi = 0",
    "C_transport^phi = 0",
]
CCFT_REQUIRED_FOLLOW_ON_ARTIFACTS = [
    "CCFT_TO_TOE_OBJECT_CROSSWALK_v0.md",
    "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0.md",
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0.md",
    "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0.md",
]
CCFT_INDEX_REVIEW_ACCEPTANCE_ITEMS = [
    "CCFT-specific C_k admissibility obligation index accepted",
    "CCFT remains candidate mesoscopic coherence bridge layer only",
    "C_source-style CCFT rows indexed",
    "C_bridge-style CCFT rows indexed",
    "C_transport-style CCFT rows indexed",
    "C_exchange-style CCFT rows indexed",
    "CCFT-ToE object crosswalk consumed as prior planning surface",
    "roadmap rebase consumed as planning-only authority",
    "local phi source/bridge/transport theorem-linkage triad preserved",
    "no proof execution",
    "no new theorem discharge",
    "no CCFT validation",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_TARGET = (
    "prepare_ccft_full_variational_action_program_packet"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_LAGRANGIAN_"
    "HAMILTONIAN_SOURCE_AND_TRANSPORT_TARGETS_NO_ACTION_EMBEDDING_OR_"
    "MASTER_ACTION_PROMOTION"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_AS_REQUIRED_PRE_"
    "DERIVATION_PLAN_NO_CK_VARIATION_OR_CCFT_VALIDATION"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_TARGET = (
    "review_ccft_full_variational_action_program_packet_result"
)
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_DEFINITION_TARGETS = [
    "CCFT full Lagrangian candidate targets",
    "CCFT full Hamiltonian candidate targets",
    "phi-sector variational route targets",
    "chi-sector variational route targets",
    "R/K rotor-curvature variational route targets",
    "CCFT stress-energy/source candidate targets",
    "CCFT C_source derivation targets",
    "CCFT C_bridge derivation targets",
    "CCFT C_transport component-derivation targets",
    "CCFT C_exchange phi-chi exchange-balance targets",
    "required blockers before action embedding",
    "required blockers before C_k variation",
    "required blockers before empirical discriminator claims",
]
CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_BOUNDARY = (
    "This packet defines a required pre-derivation planning program for CCFT "
    "Lagrangian, Hamiltonian, source, transport, and exchange target surfaces "
    "only. It does not embed C_k into an action, vary C_k, derive any C_k "
    "component, validate CCFT, authorize empirical discriminator claims, close "
    "any pillar or seam, or promote the master action."
)

NONCLAIMS = [
    "no proof execution",
    "no new theorem discharge",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no CCFT validation",
    "no master-action promotion",
]
ROADMAP_REBASE_BOUNDARY = (
    "This roadmap rebase indexes CCFT as a candidate mesoscopic coherence "
    "bridge layer only. It does not validate CCFT, promote CCFT as "
    "fundamental physics, derive CCFT from the master action, embed C_k in "
    "the action, vary C_k, close any pillar, close any seam, authorize "
    "empirical validation, or promote the master action."
)
TRIAD_BOUNDARY = (
    "This packet records only the local phi source/bridge/transport "
    "theorem-linkage triad. It is not a phi C_k rule-family closeout and "
    "does not overwrite or reinterpret the historical 2026-06-19 phi "
    "rule-family artifacts."
)


@dataclass(frozen=True)
class StageSpec:
    key: str
    schema_id: str
    packet_id: str
    status: str
    outcome_id: str
    strict_outcome_id: str
    consumed_target: str
    consumed_target_kind: str
    selected_next_target: str
    selected_next_target_kind: str
    lean_module: str
    json_filename: str
    result_kind: str
    packet_classification: str
    stage_role: str


STAGES: dict[str, StageSpec] = {
    "selector": StageSpec(
        key="selector",
        schema_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_20260702_v0"
        ),
        packet_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_v0"
        ),
        status=(
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_"
            "TRANSPORT_CLOSEOUT"
        ),
        outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_SELECTS_PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_"
            "FAMILY_SYNTHESIS_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_SELECTS_LOCAL_PHI_THEOREM_LINKAGE_TRIAD_SYNTHESIS_NO_GAP_"
            "DISCHARGE_OR_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "select_next_ck_family_theorem_linkage_obligation_after_phi_transport_"
            "closeout"
        ),
        consumed_target_kind=(
            "ck_family_theorem_linkage_obligation_selector_after_phi_transport_"
            "closeout"
        ),
        selected_next_target=(
            "review_ck_family_theorem_linkage_obligation_selection_after_phi_"
            "transport_closeout_result"
        ),
        selected_next_target_kind=(
            "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
            "closeout_result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CKFamilyTheoremLinkageObligationSelectionAfterPhiTransportCloseout"
        ),
        json_filename=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_20260702_v0.json"
        ),
        result_kind="selection",
        packet_classification=(
            "post_phi_transport_selector_selects_local_phi_theorem_linkage_triad_"
            "synthesis_only"
        ),
        stage_role="selector",
    ),
    "selector_review": StageSpec(
        key="selector_review",
        schema_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_"
            "TRANSPORT_CLOSEOUT_RESULT_REVIEW"
        ),
        outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_ACCEPTS_PHI_CK_SOURCE_BRIDGE_TRANSPORT_"
            "THEOREM_LINKAGE_FAMILY_SYNTHESIS_SELECTION_NO_PROOF_EXECUTION_OR_"
            "MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_ACCEPTS_LOCAL_PHI_THEOREM_LINKAGE_TRIAD_"
            "SYNTHESIS_SELECTION_NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "review_ck_family_theorem_linkage_obligation_selection_after_phi_"
            "transport_closeout_result"
        ),
        consumed_target_kind=(
            "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
            "closeout_result_review"
        ),
        selected_next_target=(
            "prepare_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_packet"
        ),
        selected_next_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_packet"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "CKFamilyTheoremLinkageObligationSelectionAfterPhiTransportCloseoutResultReview"
        ),
        json_filename=(
            "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_TRANSPORT_"
            "CLOSEOUT_RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "post_phi_transport_selector_review_accepts_local_phi_triad_synthesis_"
            "selection_only"
        ),
        stage_role="selector_result_review",
    ),
    "triad_packet": StageSpec(
        key="triad_packet",
        schema_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_20260702_v0"
        ),
        packet_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_v0"
        ),
        status=(
            "ACTIVE_PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_"
            "SYNTHESIS_PACKET"
        ),
        outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_PREPARED_LOCAL_TRIAD_INDEXED_NO_PHI_SECTOR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_PREPARED_C_SOURCE_C_BRIDGE_C_TRANSPORT_PHI_LOCAL_LINKAGE_"
            "ONLY_NO_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "prepare_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_packet"
        ),
        consumed_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_packet"
        ),
        selected_next_target=(
            "review_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_result"
        ),
        selected_next_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
            "result_review"
        ),
        lean_module=(
            "ToeFormal.Derivation."
            "PhiCKSourceBridgeTransportTheoremLinkageFamilySynthesisPacket"
        ),
        json_filename=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "PACKET_20260702_v0.json"
        ),
        result_kind="packet",
        packet_classification=(
            "local_phi_source_bridge_transport_theorem_linkage_triad_index_only"
        ),
        stage_role="triad_synthesis_packet",
    ),
    "triad_review": StageSpec(
        key="triad_review",
        schema_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_20260702_v0"
        ),
        packet_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_v0"
        ),
        status=(
            "ACTIVE_PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_"
            "SYNTHESIS_RESULT_REVIEW"
        ),
        outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_ACCEPTS_LOCAL_TRIAD_INDEX_NO_PHI_SECTOR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_ACCEPTS_C_SOURCE_C_BRIDGE_C_TRANSPORT_PHI_LOCAL_"
            "LINKAGE_FAMILY_NO_CK_RULE_PROMOTION"
        ),
        consumed_target=(
            "review_phi_ck_source_bridge_transport_theorem_linkage_family_"
            "synthesis_result"
        ),
        consumed_target_kind=(
            "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
            "result_review"
        ),
        selected_next_target="prepare_coherence_admissibility_bridge_roadmap_rebase_packet",
        selected_next_target_kind="coherence_admissibility_bridge_roadmap_rebase_packet",
        lean_module=(
            "ToeFormal.Derivation."
            "PhiCKSourceBridgeTransportTheoremLinkageFamilySynthesisResultReview"
        ),
        json_filename=(
            "PHI_CK_SOURCE_BRIDGE_TRANSPORT_THEOREM_LINKAGE_FAMILY_SYNTHESIS_"
            "RESULT_REVIEW_20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "local_phi_triad_synthesis_review_accepts_index_without_promotion"
        ),
        stage_role="triad_synthesis_result_review",
    ),
    "roadmap_packet": StageSpec(
        key="roadmap_packet",
        schema_id="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_20260702_v0",
        packet_id="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_v0",
        status="ACTIVE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_PACKET",
        outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_PREPARED_CCFT_AS_"
            "CANDIDATE_MESOSCOPIC_LINKAGE_LAYER_NO_PILLAR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_PREPARED_CCFT_MASTER_"
            "ACTION_CK_ARCHITECTURE_INDEXED_NO_CCFT_VALIDATION_OR_MASTER_ACTION_"
            "PROMOTION"
        ),
        consumed_target="prepare_coherence_admissibility_bridge_roadmap_rebase_packet",
        consumed_target_kind="coherence_admissibility_bridge_roadmap_rebase_packet",
        selected_next_target="review_coherence_admissibility_bridge_roadmap_rebase_result",
        selected_next_target_kind=(
            "coherence_admissibility_bridge_roadmap_rebase_result_review"
        ),
        lean_module="ToeFormal.Derivation.CoherenceAdmissibilityBridgeRoadmapRebase",
        json_filename="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_candidate_mesoscopic_bridge_layer_roadmap_rebase_planning_only"
        ),
        stage_role="roadmap_rebase_packet",
    ),
    "roadmap_review": StageSpec(
        key="roadmap_review",
        schema_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_"
            "20260702_v0"
        ),
        packet_id="COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_v0",
        status="ACTIVE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW",
        outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_ACCEPTS_"
            "CCFT_AS_CANDIDATE_MESOSCOPIC_LINKAGE_LAYER_NO_PILLAR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_ACCEPTS_"
            "CCFT_MASTER_ACTION_CK_ARCHITECTURE_INDEX_NO_CCFT_VALIDATION_OR_"
            "MASTER_ACTION_PROMOTION"
        ),
        consumed_target="review_coherence_admissibility_bridge_roadmap_rebase_result",
        consumed_target_kind=(
            "coherence_admissibility_bridge_roadmap_rebase_result_review"
        ),
        selected_next_target="prepare_ccft_to_toe_object_crosswalk_packet",
        selected_next_target_kind="ccft_to_toe_object_crosswalk_packet",
        lean_module=(
            "ToeFormal.Derivation.CoherenceAdmissibilityBridgeRoadmapRebaseResultReview"
        ),
        json_filename=(
            "COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_REBASE_RESULT_REVIEW_"
            "20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "roadmap_rebase_review_accepts_ccft_candidate_layer_planning_index_only"
        ),
        stage_role="roadmap_rebase_result_review",
    ),
    "crosswalk_packet": StageSpec(
        key="crosswalk_packet",
        schema_id="CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_20260702_v0",
        packet_id="CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_v0",
        status="ACTIVE_CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET",
        outcome_id=(
            "CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_PREPARED_MESOSCOPIC_BRIDGE_"
            "LAYER_MAPPING_NO_PILLAR_OR_SEAM_CLOSURE"
        ),
        strict_outcome_id=(
            "CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_PREPARED_OBJECT_SURFACE_"
            "MAPPING_ONLY_NO_CCFT_VALIDATION_OR_MASTER_ACTION_PROMOTION"
        ),
        consumed_target="prepare_ccft_to_toe_object_crosswalk_packet",
        consumed_target_kind="ccft_to_toe_object_crosswalk_packet",
        selected_next_target="prepare_ccft_ck_admissibility_obligation_index_packet",
        selected_next_target_kind="ccft_ck_admissibility_obligation_index_packet",
        lean_module="ToeFormal.Derivation.CCFTToTOEObjectCrosswalkPacket",
        json_filename="CCFT_TO_TOE_OBJECT_CROSSWALK_PACKET_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_to_toe_object_crosswalk_maps_candidate_surfaces_without_closure"
        ),
        stage_role="ccft_to_toe_object_crosswalk_packet",
    ),
    "ck_index_packet": StageSpec(
        key="ck_index_packet",
        schema_id="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_20260702_v0",
        packet_id="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_v0",
        status="ACTIVE_CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET",
        outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_PREPARED_SOURCE_BRIDGE_"
            "TRANSPORT_EXCHANGE_ROWS_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_PREPARED_CCFT_SPECIFIC_"
            "CK_OBLIGATIONS_ONLY_NO_CCFT_VALIDATION_OR_CK_RULE_PROMOTION"
        ),
        consumed_target="prepare_ccft_ck_admissibility_obligation_index_packet",
        consumed_target_kind="ccft_ck_admissibility_obligation_index_packet",
        selected_next_target="review_ccft_ck_admissibility_obligation_index_packet_result",
        selected_next_target_kind=(
            "ccft_ck_admissibility_obligation_index_packet_result_review"
        ),
        lean_module="ToeFormal.Derivation.CCFTCKAdmissibilityObligationIndexPacket",
        json_filename="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_specific_ck_obligation_index_source_bridge_transport_exchange_only"
        ),
        stage_role="ccft_ck_admissibility_obligation_index_packet",
    ),
    "ck_index_review": StageSpec(
        key="ck_index_review",
        schema_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_"
            "20260702_v0"
        ),
        packet_id="CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_v0",
        status="ACTIVE_CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW",
        outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_ACCEPTS_"
            "CCFT_SOURCE_BRIDGE_TRANSPORT_EXCHANGE_OBLIGATION_INDEX_NO_PROOF_"
            "EXECUTION_OR_MASTER_ACTION_PROMOTION"
        ),
        strict_outcome_id=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_ACCEPTS_"
            "CCFT_ADMISSIBILITY_ROWS_AS_PLANNING_INDEX_NO_CCFT_VALIDATION_OR_"
            "SEAM_CLOSURE"
        ),
        consumed_target="review_ccft_ck_admissibility_obligation_index_packet_result",
        consumed_target_kind=(
            "ccft_ck_admissibility_obligation_index_packet_result_review"
        ),
        selected_next_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_TARGET,
        selected_next_target_kind="ccft_full_variational_action_program_packet",
        lean_module=(
            "ToeFormal.Derivation."
            "CCFTCKAdmissibilityObligationIndexPacketResultReview"
        ),
        json_filename=(
            "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_RESULT_REVIEW_"
            "20260702_v0.json"
        ),
        result_kind="review",
        packet_classification=(
            "ccft_ck_admissibility_obligation_index_review_accepts_planning_"
            "rows_only"
        ),
        stage_role="ccft_ck_admissibility_obligation_index_packet_result_review",
    ),
    "variational_packet": StageSpec(
        key="variational_packet",
        schema_id="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_20260702_v0",
        packet_id="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_v0",
        status="ACTIVE_CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET",
        outcome_id=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME,
        strict_outcome_id=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME,
        consumed_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_TARGET,
        consumed_target_kind="ccft_full_variational_action_program_packet",
        selected_next_target=CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_REVIEW_TARGET,
        selected_next_target_kind=(
            "ccft_full_variational_action_program_packet_result_review"
        ),
        lean_module="ToeFormal.Derivation.CCFTFullVariationalActionProgramPacket",
        json_filename="CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_20260702_v0.json",
        result_kind="packet",
        packet_classification=(
            "ccft_full_variational_action_program_pre_derivation_plan_only"
        ),
        stage_role="ccft_full_variational_action_program_packet",
    ),
}

ORDERED_STAGE_KEYS = [
    "selector",
    "selector_review",
    "triad_packet",
    "triad_review",
    "roadmap_packet",
    "roadmap_review",
    "crosswalk_packet",
    "ck_index_packet",
    "ck_index_review",
    "variational_packet",
]


def release_path(spec: StageSpec) -> Path:
    return REPO_ROOT / "formal" / "docs" / "release" / spec.json_filename


def lean_path(spec: StageSpec) -> Path:
    stem = spec.lean_module.rsplit(".", 1)[-1] + ".lean"
    return REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / stem


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _result_fields(spec: StageSpec) -> dict[str, Any]:
    fields: dict[str, Any] = {
        "outcome_id": spec.outcome_id,
        "packet_result": spec.outcome_id,
        "strict_packet_result": spec.strict_outcome_id,
        "result_token": spec.outcome_id,
        "strict_result_token": spec.strict_outcome_id,
    }
    if spec.result_kind == "selection":
        fields.update(
            {
                "selection_result": spec.outcome_id,
                "selector_outcome": spec.outcome_id,
                "strict_selection_result": spec.strict_outcome_id,
                "strict_selector_outcome": spec.strict_outcome_id,
            }
        )
    if spec.result_kind == "review":
        fields.update(
            {
                "review_result": spec.outcome_id,
                "strict_review_result": spec.strict_outcome_id,
            }
        )
    return fields


def _boolean_nonclaim_flags() -> dict[str, bool]:
    return {
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "new_theorem_discharge": False,
        "theorem_linkage_obligation_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "sr_cosmo_closure_claimed": False,
        "qm_stat_closure_claimed": False,
        "pillar_closure_claim": False,
        "seam_closure_claim": False,
        "general_C_k_closure": False,
        "general_C_k_theorem_linkage_closure": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_variation_executed": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "CCFT_validated": False,
        "CCFT_fundamental_physics_claimed": False,
        "CCFT_derivation_from_master_action_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "historical_20260619_rule_family_artifacts_overwritten": False,
        "new_triad_called_rule_family_closeout": False,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
    }


def build_stage_payload(
    stage_key: str,
    *,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    spec = STAGES[stage_key]
    payload: dict[str, Any] = {
        "artifact_id": spec.schema_id,
        "schema_id": spec.schema_id,
        "packet_id": spec.packet_id,
        "status": spec.status,
        "stage_key": spec.key,
        "stage_role": spec.stage_role,
        "prepared": True,
        "accepted": True,
        "reviewed": spec.result_kind == "review",
        "selected": spec.result_kind == "selection",
        "captured_at_utc": captured_at_utc,
        "packet_classification": spec.packet_classification,
        "consumed_target": spec.consumed_target,
        "consumed_target_kind": spec.consumed_target_kind,
        "selected_next_target": spec.selected_next_target,
        "selected_next_target_kind": spec.selected_next_target_kind,
        "local_phi_triad_label": LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL,
        "local_phi_theorem_linkage_triad": LOCAL_PHI_TRIAD_EQUATIONS,
        "local_phi_theorem_linkage_triad_count": len(LOCAL_PHI_TRIAD_EQUATIONS),
        "C_source_phi_zero": "C_source^phi = 0",
        "C_bridge_phi_zero": "C_bridge^phi = 0",
        "C_transport_phi_zero": "C_transport^phi = 0",
        "triad_boundary": TRIAD_BOUNDARY,
        "roadmap_rebase_boundary": ROADMAP_REBASE_BOUNDARY,
        "nonclaims": NONCLAIMS,
        "nonclaim_count": len(NONCLAIMS),
        "lean_status_wording": LEAN_STATUS_WORDING,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES,
        "full_toeformal_aggregate_status": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "scoped_lean_targets_status": SCOPED_LEAN_TARGETS_STATUS,
        "ccft_role": "candidate mesoscopic coherence bridge layer",
        "master_action_role": "non-promoted candidate organizing surface",
        "C_k_role": "admissibility-only bridge-checking family",
        "phi_triad_role": "local theorem-linkage family only",
        "ccft_required_follow_on_artifacts": CCFT_REQUIRED_FOLLOW_ON_ARTIFACTS,
        "next_required_object": (
            "CCFT full variational/action program packet result review"
            if stage_key == "variational_packet"
            else (
                "CCFT full variational/action program packet"
                if stage_key == "ck_index_review"
                else "CCFT-to-ToE object crosswalk"
            )
        ),
        "roadmap_rebase_lists_follow_on_artifacts_only": (
            stage_key in {"roadmap_packet", "roadmap_review"}
        ),
        "later_ccft_artifacts_fully_populated": (
            stage_key
            in {
                "crosswalk_packet",
                "ck_index_packet",
                "ck_index_review",
                "variational_packet",
            }
        ),
        "CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared": stage_key in {
            "crosswalk_packet",
            "ck_index_packet",
            "ck_index_review",
            "variational_packet",
        },
        "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared": (
            stage_key in {"ck_index_packet", "ck_index_review", "variational_packet"}
        ),
        "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared": (
            stage_key == "variational_packet"
        ),
        "CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared": False,
        "files": {
            "json_report": _ptr(release_path(spec)),
            "lean_packet_file": _ptr(lean_path(spec)),
        },
        "lane_level_lean_targets": [
            spec.lean_module,
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
    }
    if stage_key == "ck_index_review":
        payload.update(
            {
                "ccft_index_review_acceptance_items": (
                    CCFT_INDEX_REVIEW_ACCEPTANCE_ITEMS
                ),
                "ccft_index_review_acceptance_item_count": len(
                    CCFT_INDEX_REVIEW_ACCEPTANCE_ITEMS
                ),
                "suggested_next_packet_outcome": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_OUTCOME
                ),
                "strict_suggested_next_packet_outcome": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_STRICT_OUTCOME
                ),
                "next_disciplined_move_reason": (
                    "The CCFT-ToE crosswalk and CCFT C_k obligation index "
                    "have now been prepared. The next disciplined move is "
                    "not proof execution yet; it is to define the "
                    "variational/action program needed before any derived "
                    "C_k component, action embedding, or transport-zero "
                    "proof can be attempted."
                ),
            }
        )
    if stage_key == "variational_packet":
        payload.update(
            {
                "ccft_full_variational_action_program_targets": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_DEFINITION_TARGETS
                ),
                "ccft_full_variational_action_program_target_count": len(
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_DEFINITION_TARGETS
                ),
                "ccft_full_variational_action_program_boundary": (
                    CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_BOUNDARY
                ),
                "ccft_lagrangian_candidate_targets_defined": True,
                "ccft_hamiltonian_candidate_targets_defined": True,
                "phi_sector_variational_route_targets_defined": True,
                "chi_sector_variational_route_targets_defined": True,
                "rotor_curvature_variational_route_targets_defined": True,
                "ccft_stress_energy_source_candidate_targets_defined": True,
                "ccft_C_source_derivation_targets_defined": True,
                "ccft_C_bridge_derivation_targets_defined": True,
                "ccft_C_transport_component_derivation_targets_defined": True,
                "ccft_C_exchange_phi_chi_exchange_balance_targets_defined": True,
                "required_blockers_before_action_embedding_defined": True,
                "required_blockers_before_C_k_variation_defined": True,
                "required_blockers_before_empirical_discriminator_claims_defined": True,
                "C_k_action_embedding_authorized": False,
                "C_k_variation_authorized": False,
                "empirical_discriminator_claims_authorized": False,
            }
        )
    payload.update(_result_fields(spec))
    payload.update(_boolean_nonclaim_flags())
    return payload


def write_stage_payload(payload: dict[str, Any], out: Path) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def stage_main(stage_key: str, argv: list[str] | None = None) -> int:
    spec = STAGES[stage_key]
    parser = argparse.ArgumentParser(description=f"Write {spec.packet_id}.")
    parser.add_argument("--out", type=Path, default=release_path(spec))
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_stage_payload(stage_key, captured_at_utc=args.captured_at_utc)
    path = write_stage_payload(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "phi_sector_closure_claimed": payload[
                    "phi_sector_closure_claimed"
                ],
                "CCFT_validated": payload["CCFT_validated"],
                "master_action_promoted": payload["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0
