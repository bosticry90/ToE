from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_ck_constraint_functional_definition_packet_report import (
    DEFAULT_OUT as CK_DEFINITION_PACKET_PATH,
    OUTCOME_ID as CK_DEFINITION_PACKET_OUTCOME,
    PACKET_RESULT as CK_DEFINITION_PACKET_RESULT,
)
from formal.python.tools.master_action_ck_constraint_functional_definition_packet_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALTERNATE_SELECTOR_PRIORITY,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POST_SELECTION_RECOMMENDED_TARGET,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_SELECTOR_PRIORITY,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTOR_CANDIDATE_SET,
    build_master_action_ck_constraint_functional_definition_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_constraint_functional_definition_packet_result_review_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_master_action_ck_definition_result_review_files_exist() -> None:
    for path in [
        CK_DEFINITION_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_master_action_ck_definition_result_review_accepts_options_index_only() -> None:
    packet = _json(CK_DEFINITION_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == CK_DEFINITION_PACKET_OUTCOME
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["ck_definition_packet_result"] == CK_DEFINITION_PACKET_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["post_selection_recommended_target"] == (
        POST_SELECTION_RECOMMENDED_TARGET
    )
    assert (
        build_master_action_ck_constraint_functional_definition_packet_result_review()
        == review
    )


def test_master_action_ck_definition_result_review_accepts_required_review_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 10
    assert review["review_criteria_accepted_count"] == 10
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "seven_ck_option_classes_indexed",
        "source_admissibility_phi_relevant_future_candidate_only",
        "bridge_admissibility_phi_relevant_future_candidate_only",
        "no_concrete_ck_family_selected",
        "no_ck_variation_executed",
        "no_phi_generation_theorem_claimed",
        "no_v_phi_derivation_claimed",
        "no_source_admissibility_or_conservation_claimed",
        "no_qft_gr_closure_or_master_action_promotion_claimed",
        "selector_next_target_selected_not_derivation",
    }
    assert review["review_accepts_options_index"] is True
    assert review["seven_ck_option_classes_indexed"] is True
    assert review["option_class_count"] == 7
    assert len(review["indexed_constraint_ids"]) == 7
    assert (
        review["source_admissibility_phi_relevant_future_candidate_only"] is True
    )
    assert review["bridge_admissibility_phi_relevant_future_candidate_only"] is True
    assert review["selector_candidate_set"] == SELECTOR_CANDIDATE_SET
    assert review["recommended_selector_priority"] == RECOMMENDED_SELECTOR_PRIORITY
    assert review["alternate_selector_priority"] == ALTERNATE_SELECTOR_PRIORITY
    assert review["source_admissibility_candidate_prioritized"] is True
    assert review["bridge_admissibility_candidate_retained_as_alternate"] is True
    assert review["selector_authorized"] is True
    assert review["derivation_authorized"] is False


def test_master_action_ck_definition_result_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["concrete_ck_family_selected"] is False
    assert review["ck_constraint_functional_family_selected"] is False
    assert review["ck_phi_relevant_constraint_class_selected"] is False
    assert review["ck_variation_executed"] is False
    assert review["ck_variation_authorized"] is False
    for key in [
        "ck_content_fully_defined_claimed",
        "phi_generation_theorem_claimed",
        "phi_generated_by_ck_claimed",
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
        "standard_model_derivation_claimed",
        "native_generation_theorem_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    assert "accepts the C_k option index only" in review["non_claim_boundary"]
    assert "C_k remains inactive and undefined" in review["non_claim_boundary"]
    assert "V(phi) remains smooth bounded-below but not derived" in (
        review["non_claim_boundary"]
    )
    assert "C_k does not yet generate phi" in review["non_claim_boundary"]


def test_master_action_ck_definition_result_review_validation_policy_records_timeout_boundary() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_master_action_ck_definition_result_review_rotates_live_target_to_selector() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "MasterActionCKConstraintFunctionalDefinitionPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_"
        "20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["concrete_ck_family_selected"] == "no"
    assert consumed["ck_variation_executed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["selector_authorized"] == "yes"
    assert active_row["selector_prepared"] == "no"
    assert active_row["derivation_authorized"] == "no"
    assert active_row["recommended_selector_priority"] == RECOMMENDED_SELECTOR_PRIORITY
    assert active_row["alternate_selector_priority"] == ALTERNATE_SELECTOR_PRIORITY
    assert active_row["post_selection_recommended_target"] == (
        POST_SELECTION_RECOMMENDED_TARGET
    )
    assert active_row["ck_constraint_functional_family_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["source_conservation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_master_action_ck_definition_result_review_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        POST_SELECTION_RECOMMENDED_TARGET,
        "MasterActionCKConstraintFunctionalDefinitionPacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: select_master_action_ck_constraint_family_for_phi_route",
        "source_admissibility_constraint",
        "bridge_admissibility_constraint",
        "selector recommendation",
        "C_k remains inactive and undefined",
        "V(phi) remains smooth bounded-below but not derived",
        "C_k does not yet generate phi",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_master_action_ck_definition_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_constraint_functional_definition_packet_result_review_gate.py"
    )
