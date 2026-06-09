from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    skip_if_not_current_target,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRStressEnergyOperatorDomainResultReview.lean"
)
OPERATOR_DOMAIN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergyOperatorDomainSemantics.lean"
)
FULL_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
)
FULL_MAP_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

CONSUMED_TARGET = "review_qft_gr_stress_energy_operator_domain_semantics_result"
NEXT_TARGET = "prepare_full_pillar_target_map_rebase"
RESULT_REVIEW_TARGET = "review_full_pillar_target_map_rebase_result"
SELECTION_TARGET = "select_next_post_rebase_bounded_attack"
SELECTED_TARGET = "prepare_qft_gr_state_expectation_functional_semantics_bounded_attack"
STATE_EXPECTATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_functional_semantics_result"
)
LIVE_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
SURFACE_ID = "qft_gr_stress_energy_operator_domain_result_review_v0"
OPERATOR_DOMAIN_SURFACE_ID = "QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_v0"
FULL_MAP_SURFACE_ID = "FULL_PILLAR_TARGET_MAP_REBASE_v0"
DECISION_ID = "pause_qft_gr_and_prepare_full_pillar_target_map_rebase"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-OPERATOR-DOMAIN-SEMANTICS-RETAINED"
)
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
OPERATOR_DOMAIN_EVIDENCE = str(OPERATOR_DOMAIN_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
FULL_MAP_EVIDENCE = str(FULL_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def test_result_review_records_bounded_pause_decision() -> None:
    text = _read(RESULT_REVIEW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DECISION_ID,
        "QFTGRStressEnergyOperatorDomainResultReviewStatus",
        "qft_gr_stress_energy_operator_domain_result_review_completed_v0",
        "qft_gr_stress_energy_operator_domain_result_review_accepts_supplied_route_v0",
        "qft_gr_stress_energy_operator_domain_result_review_package_only_refuted_v0",
        "qft_gr_stress_energy_operator_domain_result_review_retained_as_supplied_v0",
        "qft_gr_stress_energy_operator_domain_result_review_selected_decision_v0",
        "qft_gr_stress_energy_operator_domain_result_review_selected_next_target_v0",
        "qft_gr_stress_energy_operator_domain_result_review_frontier_target_v0",
        "qft_gr_stress_energy_operator_domain_result_review_same_lane_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_dependency_graph_unchanged_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_lane_unblocked_v0",
    }:
        assert token in text

    operator_domain_text = _read(OPERATOR_DOMAIN_PATH)
    assert "qft_gr_stress_energy_operator_domain_supplied_route_available_v0" in operator_domain_text
    assert "qft_gr_stress_energy_operator_domain_package_only_refuted_v0" in operator_domain_text
    assert "qft_gr_stress_energy_operator_domain_retained_as_supplied_v0" in operator_domain_text


def test_result_review_preserves_fail_closed_boundaries() -> None:
    text = _read(RESULT_REVIEW_PATH)

    for theorem in {
        "qft_gr_stress_energy_operator_domain_result_review_no_broader_theorem_work_v0",
        "qft_gr_stress_energy_operator_domain_result_review_expectation_functional_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_renormalized_expectation_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_weak_curvature_source_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_covariance_conservation_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_full_source_map_closure_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_seam_closure_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_semiclassical_gravity_claim_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_einstein_equation_claim_v0",
        "qft_gr_stress_energy_operator_domain_result_review_phase2_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_result_review_master_action_not_promoted_v0",
        "qft_gr_stress_energy_operator_domain_result_review_no_empirical_claim_v0",
        "qft_gr_stress_energy_operator_domain_result_review_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_rotate_to_full_target_map_rebase() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert "import ToeFormal.Derivation.QFTGRStressEnergyOperatorDomainResultReview" in aggregate_text
    assert "import ToeFormal.Derivation.FullPillarTargetMapRebase" in aggregate_text
    assert "QFT-GR state expectation-functional result review completed" in frontier_text
    assert (
        "operator-domain assumption-reduction closeout packet" in frontier_text
        or "weak/strong conservation comparison scope assumption-reduction packet" in frontier_text
    )
    assert LIVE_TARGET in frontier_text


def test_loop_registry_tracks_result_review_pause_and_full_map_rebase() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()
    payload = _registry()
    skip_if_not_current_target(payload, LIVE_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == STATE_EXPECTATION_RESULT_REVIEW_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert (
        state["active_lane"]
        == "qft_gr_renormalized_expectation_value_semantics_preparation"
    )

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["status"] == "paused"
    assert qft_gr["stress_energy_operator_domain_result_review_decision"] == DECISION_ID
    assert qft_gr["stress_energy_operator_domain_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert qft_gr["stress_energy_operator_domain_result_review_status"] == "completed"
    assert qft_gr["stress_energy_operator_domain_result_review_evidence"] == RESULT_REVIEW_EVIDENCE
    assert qft_gr["stress_energy_operator_domain_result_review_decision"] == DECISION_ID
    assert qft_gr["authorized_next_strict_target"] == LIVE_TARGET
    assert qft_gr["theorem_work_authorized"] == (
        "preparation_only_for_renormalized_expectation_value_semantics"
    )
    assert qft_gr["same_lane_continuation"] == (
        "preparation_only_no_renormalized_expectation_claim"
    )
    assert qft_gr["qft_state_expectation_functional_semantics_authorized"] == (
        "supplied_only_retained"
    )
    assert qft_gr["renormalized_expectation_semantics_authorized"] == "no"
    assert qft_gr["gr_weak_curvature_source_identification_semantics_authorized"] == "no"
    assert qft_gr["covariance_conservation_semantics_authorized"] == "no"
    assert qft_gr["full_source_map_semantic_closure_authorized"] == "no"

    master_action = workstream("master_action_dependency_frontier", payload)
    assert master_action["status"] == "paused"
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_status"] == (
        "completed"
    )
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_evidence"] == (
        RESULT_REVIEW_EVIDENCE
    )
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_decision"] == (
        DECISION_ID
    )
    assert master_action["authorized_next_strict_target"] == LIVE_TARGET
    assert master_action["promotion_authorized"] == "no"

    full_map = workstream("full_pillar_target_map_rebase", payload)
    assert full_map["status"] == "paused"
    assert full_map["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert full_map["authorization_evidence"] == RESULT_REVIEW_EVIDENCE
    assert full_map["target_map_evidence"] == FULL_MAP_EVIDENCE
    assert full_map["target_map_document"] == (
        "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
    )
    assert full_map["route_source_required"] == "yes"
    assert full_map["completion_scale_required"] == "yes"
    assert full_map["claim_posture_taxonomy_bound"] == "yes"
    assert full_map["master_action_status"] == "MASTER_ACTION_CITATION_BOUND"
    assert full_map["full_pillar_completion_claim"] == "no"
    assert full_map["theorem_work_authorized"] == (
        "result_review_only_after_target_map_rebase"
    )

    active_review = workstream("full_pillar_target_map_rebase_result_review", payload)
    assert active_review["status"] == "paused"
    assert active_review["authorized_next_strict_target"] == SELECTION_TARGET
    assert active_review["consumed_target"] == NEXT_TARGET
    assert active_review["target_map_authority_only"] == "yes"
    assert active_review["next_physics_attack_selected"] == "no"

    selection = workstream("post_rebase_next_bounded_attack_selection", payload)
    assert selection["status"] == "paused"
    assert selection["authorized_next_strict_target"] == SELECTED_TARGET
    assert selection["selection_executes_attack"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_stress_energy_operator_domain_semantics",
        "qft_gr_stress_energy_operator_domain_semantics_result_review",
    ) in edges
    assert (
        "qft_gr_stress_energy_operator_domain_semantics_result_review",
        "full_pillar_target_map_rebase",
    ) in edges


def test_public_surfaces_and_manifest_boundary_are_synchronized() -> None:
    assert_public_surfaces_match_registry()

    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QFTGRStressEnergyOperatorDomainResultReview.lean" in text
        assert "FullPillarTargetMapRebase.lean" in text or FULL_MAP_SURFACE_ID in text
        assert CONSUMED_TARGET in text
        if path in {ROADMAP_PATH, STRICT_MAP_PATH}:
            assert NEXT_TARGET in text
            assert SELECTION_TARGET in text
            assert STATE_EXPECTATION_RESULT_REVIEW_TARGET in text
        assert LIVE_TARGET in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_RESULT_REVIEW_STATUS_v0" in text
        assert FULL_MAP_SURFACE_ID in text
        assert NEXT_TARGET in text
        assert STATE_EXPECTATION_RESULT_REVIEW_TARGET in text
        assert LIVE_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-STRESS-ENERGY-OPERATOR-DOMAIN-RESULT-REVIEW-v0" in inventory_text
    assert "INV-MATH-FULL-PILLAR-TARGET-MAP-REBASE-v0" in inventory_text
    assert RESULT_REVIEW_EVIDENCE in inventory_text
    assert OPERATOR_DOMAIN_EVIDENCE in inventory_text
    assert FULL_MAP_EVIDENCE in inventory_text

    assert FULL_MAP_DOC_PATH.exists()
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_stress_energy_operator_domain_result_review_gate.py"
    )
