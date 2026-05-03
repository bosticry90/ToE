from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    GOVERNANCE_MANIFEST_PATH,
    README_PATH,
    REGISTRY_PATH,
    REPO_ROOT,
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CrossPillarClosureFrontier.lean"
)
POST_SWEEP_QUEUE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "PostSweepTheoremQueue.lean"
)
QM_EVOLUTION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMEvolutionPostBudgetCrossPillarReview.lean"
)
EM_QFT_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPhysicsBlockerProtocolRow.lean"
)
EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_SharedDynamicsResidualUnificationBridge.lean"
)
EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_InterfaceAlignmentSemanticBridge.lean"
)
EM_QFT_POST_BUDGET_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPostBudgetCrossPillarReview.lean"
)
MASTER_ACTION_CITATION_USAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedAssumptionCitationUsage.lean"
)
MASTER_ACTION_CITATION_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCitationLanguageAudit.lean"
)
MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGraphReview.lean"
)
MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedBlockerPrioritizationReview.lean"
)
QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean"
)
QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
)
QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_SourceProbabilityExtractionSemantics.lean"
)
QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATSourceProbabilityExtractionResultReview.lean"
)
MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionPostQMSTATRetainedBlockerPrioritizationReview.lean"
)
QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsRetainedBlockerProtocolRow.lean"
)

CITATION_USAGE_TARGET = "cite_only_bounded_retained_assumptions"
AUDIT_TARGET = "audit_master_action_citation_language_against_retained_boundaries"
REVIEW_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
PROTOCOL_PREPARATION_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
SOURCE_PROBABILITY_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
SOURCE_PROBABILITY_RESULT_REVIEW_TARGET = (
    "review_qm_stat_source_probability_extraction_semantics_result"
)
POST_QMSTAT_PRIORITIZATION_TARGET = (
    "prioritize_retained_blockers_after_qm_stat_source_probability_result_review"
)
QFT_GR_PROTOCOL_ROW_PREPARATION_TARGET = (
    "prepare_qft_gr_source_map_semantics_retained_blocker_protocol_row"
)
QFT_GR_PROTOCOL_ROW_READINESS_REVIEW_TARGET = (
    "review_qft_gr_source_map_semantics_protocol_row_readiness"
)
LIVE_TARGET = QFT_GR_PROTOCOL_ROW_READINESS_REVIEW_TARGET
PREVIOUS_TARGET = QFT_GR_PROTOCOL_ROW_PREPARATION_TARGET
EM_QFT_POST_BUDGET_TARGET = "em_qft_post_budget_cross_pillar_review"
INTERFACE_TARGET = "derive_or_refute_em_qft_interface_alignment_semantic_bridge"
SHARED_DYNAMICS_TARGET = "derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge"
EXTRACTION_TARGET = "extract_em_qft_physics_blocker_into_protocol_row"
QM_REVIEW_TARGET = "qm_evolution_post_budget_cross_pillar_review"
STALE_SCALAR_ACTION = "derive_or_refute_evolution_to_transport_semantic_bridge"
SCALAR_PAUSED_ACTION = "paused_no_scalar_reopen_until_dependency_graph_change"
HISTORICAL_QUEUE_TOKEN = "HISTORICAL_NONLIVE_FIRST_WAVE_QUEUE_v0"
CURRENT_TARGET_TOKEN = f"CURRENT_LIVE_NEXT_TARGET_v0: {LIVE_TARGET}"
EM_QFT_PRIMARY_BLOCKER = "shared_dynamics_and_residual_unification"
EM_QFT_SECONDARY_BLOCKER = "interface_alignment_semantic_bridge"
EM_QFT_FRESH_DELTA_ID = (
    "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_COUNTEREXAMPLE_FRESH_DELTA_v0"
)

PAUSED_LANES = {
    "scalar_qft_a2a15a1",
    "qft_gr_source_map",
    "sr_covariance_cosmology_regime_transport",
    "qm_evolution_contract",
    "em_qft_physics_blocker_extraction",
    "qm_stat_transport_residual",
}
FORBIDDEN_ASSERTIONS = {
    "phase2_authorized",
    "seam_closure_claimed",
    "master_action_promoted",
    "empirical_claimed",
    "governance_manifest_enrollment_authorized",
}


def _read(path: Path) -> str:
    return read_text(path)


def _registry() -> dict[str, Any]:
    return loop_registry()


def _control(payload: dict[str, Any], control_id: str) -> dict[str, Any]:
    for control in payload["controls"]:
        if control["control_id"] == control_id:
            return control
    raise AssertionError(f"Missing control: {control_id}")


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    return workstream(workstream_id, payload)


def _iter_key_values(value: Any, path: tuple[str, ...] = ()) -> list[tuple[tuple[str, ...], Any]]:
    if isinstance(value, dict):
        pairs: list[tuple[tuple[str, ...], Any]] = []
        for key, child in value.items():
            pairs.extend(_iter_key_values(child, path + (str(key),)))
        return pairs
    if isinstance(value, list):
        pairs = []
        for index, child in enumerate(value):
            pairs.extend(_iter_key_values(child, path + (str(index),)))
        return pairs
    return [(path, value)]


def test_single_live_target_is_machine_pinned_after_qm_review() -> None:
    assert_current_target_consistent()
    payload = _registry()
    state = payload["current_target_state"]

    assert state["schema_id"] == "CURRENT_TARGET_STATE_v0"
    assert state["previous_live_next_target"] == PREVIOUS_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["post_sweep_queue_authority_status"] == HISTORICAL_QUEUE_TOKEN
    assert set(state["paused_lanes"]) == PAUSED_LANES
    assert state["active_lane"] == "master_action_dependency_frontier"

    current_active_workstream = active_workstream(payload)
    assert current_active_workstream["workstream_id"] == "master_action_dependency_frontier"
    assert current_active_workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert current_active_workstream["consumed_target"] == PREVIOUS_TARGET
    assert (
        current_active_workstream["latest_surface"]
        == "qft_gr_source_map_semantics_retained_blocker_protocol_row_v0"
    )
    assert (
        current_active_workstream["same_lane_continuation"]
        == "qft_gr_protocol_row_readiness_review_only"
    )

    active_targets = {state["live_next_target"], current_active_workstream["authorized_next_strict_target"]}
    assert active_targets == {LIVE_TARGET}


def test_readme_registry_and_frontier_agree_on_live_target() -> None:
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    payload = _registry()
    readme_text = _read(README_PATH)
    frontier_text = _read(CROSS_PILLAR_FRONTIER_PATH)
    review_text = _read(QM_EVOLUTION_REVIEW_PATH)
    protocol_text = _read(EM_QFT_PROTOCOL_ROW_PATH)
    shared_bridge_text = _read(EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH)
    interface_bridge_text = _read(EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_PATH)
    em_qft_review_text = _read(EM_QFT_POST_BUDGET_REVIEW_PATH)
    citation_usage_text = _read(MASTER_ACTION_CITATION_USAGE_PATH)
    citation_audit_text = _read(MASTER_ACTION_CITATION_AUDIT_PATH)
    dependency_graph_review_text = _read(MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH)
    prioritization_review_text = _read(
        MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH
    )
    protocol_row_text = _read(QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW_PATH)
    source_probability_text = _read(QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH)
    source_probability_review_text = _read(QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH)
    post_qm_stat_prioritization_text = _read(
        MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH
    )
    qft_gr_protocol_row_text = _read(QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH)

    assert CURRENT_TARGET_TOKEN in readme_text
    assert f'"live_next_target": "{LIVE_TARGET}"' in _read(REGISTRY_PATH)
    assert (
        'def currentLiveNextStrictTargetV0 : String :=\n'
        f'  "{LIVE_TARGET}"'
    ) in frontier_text
    assert (
        'def previousLiveNextStrictTargetV0 : String :=\n'
        f'  "{PREVIOUS_TARGET}"'
    ) in frontier_text
    assert (
        'def emQFTPhysicsBlockerExtractionTargetId : String :=\n'
        f'  "{EXTRACTION_TARGET}"'
    ) in review_text
    assert (
        'def emQFTSharedDynamicsResidualUnificationBridgeTargetId : String :=\n'
        f'  "{SHARED_DYNAMICS_TARGET}"'
    ) in protocol_text
    assert (
        'def emQFTInterfaceAlignmentSemanticBridgeTargetId : String :=\n'
        f'  "{INTERFACE_TARGET}"'
    ) in shared_bridge_text
    assert (
        'def emQFTPostBudgetCrossPillarReviewTargetId : String :=\n'
        f'  "{EM_QFT_POST_BUDGET_TARGET}"'
    ) in interface_bridge_text
    assert (
        'def masterActionCitationBoundaryTargetId : String :=\n'
        f'  "{CITATION_USAGE_TARGET}"'
    ) in em_qft_review_text
    assert (
        'def masterActionCitationUsageConsumedTargetId : String :=\n'
        f'  "{CITATION_USAGE_TARGET}"'
    ) in citation_usage_text
    assert (
        'def masterActionCitationLanguageAuditTargetId : String :=\n'
        f'  "{AUDIT_TARGET}"'
    ) in citation_usage_text
    assert (
        'def masterActionCitationLanguageAuditConsumedTargetId : String :=\n'
        f'  "{AUDIT_TARGET}"'
    ) in citation_audit_text
    assert (
        'def masterActionPostCitationAuditReviewTargetId : String :=\n'
        f'  "{REVIEW_TARGET}"'
    ) in citation_audit_text
    assert (
        'def masterActionDependencyGraphReviewConsumedTargetId : String :=\n'
        f'  "{REVIEW_TARGET}"'
    ) in dependency_graph_review_text
    assert (
        'def retainedBlockerPrioritizationReviewTargetId : String :=\n'
        f'  "{PRIORITIZATION_TARGET}"'
    ) in dependency_graph_review_text
    assert (
        'def retainedBlockerPrioritizationConsumedTargetId : String :=\n'
        f'  "{PRIORITIZATION_TARGET}"'
    ) in prioritization_review_text
    assert (
        'def qmStatTransportProtocolRowPreparationTargetId : String :=\n'
        f'  "{PROTOCOL_PREPARATION_TARGET}"'
    ) in prioritization_review_text
    assert (
        'def qmStatTransportSemanticsProtocolRowConsumedTargetId : String :=\n'
        f'  "{PROTOCOL_PREPARATION_TARGET}"'
    ) in protocol_row_text
    assert (
        'def qmStatTransportSemanticsReadinessReviewTargetId : String :=\n'
        f'  "{READINESS_REVIEW_TARGET}"'
    ) in protocol_row_text
    readiness_review_text = _read(QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW_PATH)
    assert (
        'def qmStatTransportSemanticsReadinessReviewConsumedTargetId : String :=\n'
        "  qmStatTransportSemanticsReadinessReviewTargetId"
    ) in readiness_review_text
    assert (
        'def qmStatSourceProbabilityExtractionSemanticsTargetId : String :=\n'
        f'  "{SOURCE_PROBABILITY_TARGET}"'
    ) in readiness_review_text
    assert (
        'def qmStatSourceProbabilityExtractionResultReviewTargetId : String :=\n'
        f'  "{SOURCE_PROBABILITY_RESULT_REVIEW_TARGET}"'
    ) in source_probability_text
    assert (
        'def qmStatSourceProbabilityExtractionResultReviewConsumedTargetId : String :=\n'
        "  qmStatSourceProbabilityExtractionResultReviewTargetId"
    ) in source_probability_review_text
    assert (
        'def qmStatPostSourceProbabilityRetainedBlockerPrioritizationTargetId : String :=\n'
        f'  "{POST_QMSTAT_PRIORITIZATION_TARGET}"'
    ) in source_probability_review_text
    assert (
        'def postQMSTATRetainedBlockerPrioritizationConsumedTargetId : String :=\n'
        "  qmStatPostSourceProbabilityRetainedBlockerPrioritizationTargetId"
    ) in post_qm_stat_prioritization_text
    assert (
        'def qftGRSourceMapProtocolRowPreparationTargetId : String :=\n'
        f'  "{PREVIOUS_TARGET}"'
    ) in post_qm_stat_prioritization_text
    assert (
        'def qftGRSourceMapSemanticsProtocolRowConsumedTargetId : String :=\n'
        "  qftGRSourceMapProtocolRowPreparationTargetId"
    ) in qft_gr_protocol_row_text
    assert (
        'def qftGRSourceMapSemanticsReadinessReviewTargetId : String :=\n'
        f'  "{LIVE_TARGET}"'
    ) in qft_gr_protocol_row_text
    assert payload["current_target_state"]["live_next_target"] == LIVE_TARGET


def test_no_stale_live_next_action_survives_in_registry() -> None:
    payload = _registry()
    scalar = _control(payload, "scalar_post_capstone_anti_loop")
    assert scalar["status"] == "paused"
    assert scalar["next_action"] == SCALAR_PAUSED_ACTION

    stale_live_paths: list[str] = []
    checked_key_suffixes = {"next_action", "next_strict_target", "next_action_after_retention"}
    for path, value in _iter_key_values(payload):
        if path and path[-1] in checked_key_suffixes and value == STALE_SCALAR_ACTION:
            stale_live_paths.append(".".join(path))
    assert not stale_live_paths, (
        "Completed bridge target still appears as a live next action: "
        + ", ".join(stale_live_paths)
    )

    qm_evolution = _workstream(payload, "qm_evolution_contract")
    assert qm_evolution["post_budget_review_status"] == "completed"
    assert qm_evolution["same_lane_continuation"] == "not_authorized"
    assert qm_evolution["next_strict_target"] == EXTRACTION_TARGET
    assert qm_evolution["next_action_after_retention"] == EXTRACTION_TARGET
    assert qm_evolution["stronger_qm_dynamics_bridge_derivation"] == "not_supplied"

    em_qft = _workstream(payload, "em_qft_physics_blocker_extraction")
    assert em_qft["status"] == "paused"
    assert em_qft["post_budget_review_status"] == "completed"
    assert em_qft["post_budget_review_evidence"] == str(
        EM_QFT_POST_BUDGET_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert em_qft["same_lane_continuation"] == "not_authorized_attempt_budget_reached"
    assert em_qft["source_current_bridge_slice_authorized"] == "not_authorized"
    assert em_qft["gauge_quantization_bridge_slice_authorized"] == "not_authorized"

    qft_gr = _workstream(payload, "qft_gr_source_map")
    assert qft_gr["status"] == "paused"
    assert qft_gr["protocol_row_preparation_target"] == PREVIOUS_TARGET
    assert (
        qft_gr["protocol_row_preparation_status"]
        == "completed_protocol_row_prepared"
    )
    assert qft_gr["protocol_row_preparation_authorized"] == "preparation_only_no_theorem_work"
    assert qft_gr["protocol_row_status"] == "prepared_from_post_qm_stat_prioritization"
    assert qft_gr["protocol_row_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qft_gr["protocol_row_next_review"] == LIVE_TARGET
    assert qft_gr["source_map_semantics_primary_blocker"] == "full_source_map_semantic_closure"
    assert qft_gr["stress_energy_operator_domain_obligation"] == "still_required"
    assert qft_gr["qft_state_expectation_functional_obligation"] == "still_required"
    assert qft_gr["renormalized_expectation_obligation"] == "still_required"
    assert qft_gr["gr_weak_curvature_source_identification_obligation"] == "still_required"
    assert qft_gr["covariance_conservation_obligation"] == "still_required"
    assert qft_gr["readiness_review_status"] == "pending"
    assert qft_gr["theorem_work_authorized"] == (
        "no_protocol_row_prepared_readiness_review_pending"
    )

    qm_stat = _workstream(payload, "qm_stat_transport_residual")
    assert qm_stat["status"] == "paused"
    assert qm_stat["authorized_next_strict_target"] == POST_QMSTAT_PRIORITIZATION_TARGET
    assert qm_stat["authorization_evidence"] == str(
        QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert qm_stat["latest_surface"] == "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"
    assert qm_stat["bounded_source_probability_slice_authorized"] == "completed"
    assert qm_stat["source_probability_extraction_contract_only_refuted"] == "yes"
    assert qm_stat["source_probability_extraction_derived_from_contract_alone"] == "no"
    assert qm_stat["theorem_work_authorized"] == "no_result_review_completed_same_lane_paused"
    assert qm_stat["source_probability_result_review_status"] == "completed"
    assert qm_stat["source_probability_result_review_evidence"] == str(
        QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        qm_stat["source_probability_result_review_decision"]
        == "pause_qm_stat_and_prioritize_retained_blockers"
    )
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"
    assert qm_stat["coarse_graining_irreversibility_authorized"] == "no"
    assert qm_stat["residual_package_semantic_closure_authorized"] == "no"

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["status"] == "active"
    assert master_action["citation_usage_status"] == "completed"
    assert master_action["citation_language_audit_status"] == "completed"
    assert master_action["dependency_graph_review_status"] == "completed"
    assert master_action["qm_stat_transport_semantics_protocol_row_status"] == "prepared"
    assert master_action["readiness_review_status"] == "completed"
    assert master_action["source_probability_extraction_status"] == (
        "completed_supplied_route_available_contract_only_refuted"
    )
    assert master_action["source_probability_result_review_status"] == "completed"
    assert master_action["source_probability_result_review_evidence"] == str(
        QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        master_action["source_probability_result_review_decision"]
        == "pause_qm_stat_and_prioritize_retained_blockers"
    )
    assert master_action["post_qm_stat_retained_blocker_prioritization_status"] == "completed"
    assert master_action["post_qm_stat_retained_blocker_prioritization_evidence"] == str(
        MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert (
        master_action["post_qm_stat_top_retained_blocker"]
        == "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED"
    )
    assert master_action["qft_gr_source_map_protocol_row_preparation_target"] == PREVIOUS_TARGET
    assert (
        master_action["qft_gr_source_map_protocol_row_preparation_status"]
        == "completed_protocol_row_prepared"
    )
    assert master_action["qft_gr_source_map_protocol_row_status"] == "prepared"
    assert master_action["qft_gr_protocol_row_authority_row"] == "ROW-SEAM-QFT-GR-001"
    assert master_action["qft_gr_protocol_row_seam"] == "SEAM-QFT-GR"
    assert master_action["qft_gr_protocol_row_next_review"] == LIVE_TARGET
    assert master_action["qft_gr_protocol_row_evidence"] == str(
        QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert master_action["qft_gr_protocol_row_primary_blocker"] == (
        "full_source_map_semantic_closure"
    )
    assert master_action["theorem_work_authorized"] == (
        "no_qft_gr_protocol_row_prepared_readiness_review_pending"
    )
    assert master_action["dependency_graph_changed"] == "no"
    assert master_action["lane_unblocked"] == "no"
    assert master_action["promotion_authorized"] == "no"


def test_paused_lanes_do_not_advertise_active_continuation() -> None:
    payload = _registry()

    for lane in PAUSED_LANES:
        workstream = _workstream(payload, lane)
        assert workstream["status"] == "paused", lane

        continuation_values = [
            value
            for key, value in workstream.items()
            if "continuation" in key or key.endswith("_reopen") or key == "same_lane_continuation"
        ]
        assert "authorized" not in continuation_values, lane

    assert _workstream(payload, "qm_evolution_contract")["scalar_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["qm_stat_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["qft_gr_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["sr_cosmo_reopen"] == "not_authorized"


def test_historical_post_sweep_queue_cannot_override_live_target() -> None:
    payload = _registry()
    queue_text = _read(POST_SWEEP_QUEUE_PATH)

    assert HISTORICAL_QUEUE_TOKEN in queue_text
    assert "live_next_target_source := False" in queue_text
    assert (
        _control(payload, "post_sweep_queue_discipline")["authority_status"]
        == HISTORICAL_QUEUE_TOKEN
    )
    assert _control(payload, "post_sweep_queue_discipline")["live_next_target_authority"] is False

    historical_targets = set(re.findall(r'target\s*:=\s*"([^"]+)"', queue_text))
    assert historical_targets
    assert LIVE_TARGET not in historical_targets
    assert PREVIOUS_TARGET not in historical_targets
    assert SOURCE_PROBABILITY_TARGET not in historical_targets
    assert PRIORITIZATION_TARGET not in historical_targets
    assert CITATION_USAGE_TARGET not in historical_targets
    assert EM_QFT_POST_BUDGET_TARGET not in historical_targets
    assert INTERFACE_TARGET not in historical_targets
    assert SHARED_DYNAMICS_TARGET not in historical_targets
    assert EXTRACTION_TARGET not in historical_targets
    assert QM_REVIEW_TARGET not in historical_targets


def test_forbidden_promotion_boundaries_remain_fail_closed() -> None:
    assert_forbidden_promotions_closed()
    payload = _registry()
    assertions = payload["non_promotion_assertions"]
    assert set(assertions) == FORBIDDEN_ASSERTIONS
    assert not any(assertions.values())

    state = payload["current_target_state"]
    assert set(state["forbidden_promotions"]) == {
        "phase2_authorization",
        "seam_closure",
        "empirical_claim",
        "master_action_promotion",
        "governance_manifest_enrollment",
    }

    protocol_text = _read(EM_QFT_PROTOCOL_ROW_PATH)
    shared_bridge_text = _read(EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH)
    interface_bridge_text = _read(EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_PATH)
    em_qft_review_text = _read(EM_QFT_POST_BUDGET_REVIEW_PATH)
    citation_usage_text = _read(MASTER_ACTION_CITATION_USAGE_PATH)
    citation_audit_text = _read(MASTER_ACTION_CITATION_AUDIT_PATH)
    dependency_graph_review_text = _read(MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH)
    prioritization_review_text = _read(
        MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH
    )
    protocol_row_text = _read(QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW_PATH)
    readiness_review_text = _read(QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW_PATH)
    source_probability_text = _read(QM_STAT_SOURCE_PROBABILITY_EXTRACTION_PATH)
    source_probability_review_text = _read(QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_PATH)
    post_qm_stat_prioritization_text = _read(
        MASTER_ACTION_POST_QMSTAT_PRIORITIZATION_REVIEW_PATH
    )
    qft_gr_protocol_row_text = _read(QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW_PATH)
    for theorem_name in [
        "em_qft_protocol_row_phase2_not_authorized_v0",
        "em_qft_protocol_row_seam_not_closed_v0",
        "em_qft_protocol_row_master_action_not_promoted_v0",
        "em_qft_protocol_row_no_empirical_claim_v0",
        "em_qft_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in protocol_text
    for theorem_name in [
        "em_qft_shared_dynamics_phase2_not_authorized_v0",
        "em_qft_shared_dynamics_no_seam_closure_v0",
        "em_qft_shared_dynamics_master_action_not_promoted_v0",
        "em_qft_shared_dynamics_no_empirical_claim_v0",
        "em_qft_shared_dynamics_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in shared_bridge_text
    for theorem_name in [
        "em_qft_interface_alignment_phase2_not_authorized_v0",
        "em_qft_interface_alignment_no_seam_closure_v0",
        "em_qft_interface_alignment_master_action_not_promoted_v0",
        "em_qft_interface_alignment_no_empirical_claim_v0",
        "em_qft_interface_alignment_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in interface_bridge_text
    for theorem_name in [
        "em_qft_post_budget_phase2_not_authorized_v0",
        "em_qft_post_budget_em_qft_seam_not_closed_v0",
        "em_qft_post_budget_master_action_not_promoted_v0",
        "em_qft_post_budget_no_empirical_claim_v0",
        "em_qft_post_budget_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in em_qft_review_text
    for theorem_name in [
        "master_action_citation_usage_no_seam_closure_v0",
        "master_action_citation_usage_phase2_not_authorized_v0",
        "master_action_citation_usage_master_action_not_promoted_v0",
        "master_action_citation_usage_no_empirical_claim_v0",
        "master_action_citation_usage_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in citation_usage_text
    for theorem_name in [
        "master_action_citation_language_audit_no_seam_closure_v0",
        "master_action_citation_language_audit_phase2_not_authorized_v0",
        "master_action_citation_language_audit_master_action_not_promoted_v0",
        "master_action_citation_language_audit_no_empirical_claim_v0",
        "master_action_citation_language_audit_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in citation_audit_text
    for theorem_name in [
        "master_action_dependency_graph_review_no_seam_closure_v0",
        "master_action_dependency_graph_review_phase2_not_authorized_v0",
        "master_action_dependency_graph_review_master_action_not_promoted_v0",
        "master_action_dependency_graph_review_no_empirical_claim_v0",
        "master_action_dependency_graph_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in dependency_graph_review_text
    for theorem_name in [
        "retained_blocker_prioritization_no_seam_closure_v0",
        "retained_blocker_prioritization_phase2_not_authorized_v0",
        "retained_blocker_prioritization_master_action_not_promoted_v0",
        "retained_blocker_prioritization_no_empirical_claim_v0",
        "retained_blocker_prioritization_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in prioritization_review_text
    for theorem_name in [
        "qm_stat_transport_semantics_protocol_row_no_seam_closure_v0",
        "qm_stat_transport_semantics_protocol_row_phase2_not_authorized_v0",
        "qm_stat_transport_semantics_protocol_row_master_action_not_promoted_v0",
        "qm_stat_transport_semantics_protocol_row_no_empirical_claim_v0",
        "qm_stat_transport_semantics_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in protocol_row_text
    for theorem_name in [
        "qm_stat_transport_semantics_readiness_review_no_seam_closure_v0",
        "qm_stat_transport_semantics_readiness_review_no_stat_mechanics_claim_v0",
        "qm_stat_transport_semantics_readiness_review_phase2_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_master_action_not_promoted_v0",
        "qm_stat_transport_semantics_readiness_review_no_empirical_claim_v0",
        "qm_stat_transport_semantics_readiness_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in readiness_review_text
    for theorem_name in [
        "qm_stat_source_probability_extraction_no_seam_closure_v0",
        "qm_stat_source_probability_extraction_no_stat_mechanics_claim_v0",
        "qm_stat_source_probability_extraction_phase2_not_authorized_v0",
        "qm_stat_source_probability_extraction_master_action_not_promoted_v0",
        "qm_stat_source_probability_extraction_no_empirical_claim_v0",
        "qm_stat_source_probability_extraction_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in source_probability_text
    for theorem_name in [
        "qm_stat_source_probability_result_review_no_seam_closure_v0",
        "qm_stat_source_probability_result_review_no_stat_mechanics_claim_v0",
        "qm_stat_source_probability_result_review_phase2_not_authorized_v0",
        "qm_stat_source_probability_result_review_master_action_not_promoted_v0",
        "qm_stat_source_probability_result_review_no_empirical_claim_v0",
        "qm_stat_source_probability_result_review_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in source_probability_review_text
    for theorem_name in [
        "post_qm_stat_retained_blocker_prioritization_no_qft_gr_seam_closure_v0",
        "post_qm_stat_retained_blocker_prioritization_no_semiclassical_gravity_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_no_einstein_equation_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_phase2_not_authorized_v0",
        "post_qm_stat_retained_blocker_prioritization_master_action_not_promoted_v0",
        "post_qm_stat_retained_blocker_prioritization_no_empirical_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in post_qm_stat_prioritization_text
    for theorem_name in [
        "qft_gr_source_map_semantics_protocol_row_no_seam_closure_v0",
        "qft_gr_source_map_semantics_protocol_row_no_semiclassical_gravity_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_no_einstein_equation_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_phase2_not_authorized_v0",
        "qft_gr_source_map_semantics_protocol_row_master_action_not_promoted_v0",
        "qft_gr_source_map_semantics_protocol_row_no_empirical_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in qft_gr_protocol_row_text


def test_current_target_gate_is_not_governance_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled("test_current_target_freshness_gate.py")
