from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.ck_constraint_family_selection_after_phi_source_and_bridge_admissibility_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_CK_SYNTHESIS_CLOSEOUT_OUTCOME,
    PHI_CK_SYNTHESIS_CLOSEOUT_PATH,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SELECTION_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    TRANSPORT_CANDIDATE_PLAIN_MEANING,
    TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
    TRANSPORT_CHAIN_FORM,
    TRANSPORT_CHAIN_STEPS,
    TRANSPORT_CONSISTENCY_QUESTION,
    build_ck_constraint_family_selection_after_phi_source_and_bridge_admissibility,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_constraint_family_selection_after_phi_source_and_bridge_admissibility_report.py"
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


def test_ck_constraint_family_selection_files_exist() -> None:
    for path in [
        PHI_CK_SYNTHESIS_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_ck_constraint_family_selection_accepts_source_bridge_closeout() -> None:
    closeout = _json(PHI_CK_SYNTHESIS_CLOSEOUT_PATH)
    selection = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == PHI_CK_SYNTHESIS_CLOSEOUT_OUTCOME
    assert closeout["selected_next_target"] == CONSUMED_TARGET
    assert selection["artifact_id"] == ARTIFACT_ID
    assert selection["schema_id"] == SCHEMA_ID
    assert selection["packet_id"] == PACKET_ID
    assert selection["prepared"] is True
    assert selection["accepted"] is True
    assert selection["outcome_id"] == OUTCOME_ID
    assert selection["selection_result"] == SELECTION_RESULT
    assert selection["packet_classification"] == PACKET_CLASSIFICATION
    assert selection["consumed_target"] == CONSUMED_TARGET
    assert selection["selected_next_target"] == NEXT_TARGET
    assert selection["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_ck_constraint_family_selection_after_phi_source_and_bridge_admissibility()
        == selection
    )


def test_ck_constraint_family_selection_preserves_source_and_bridge_context() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert selection["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert (
        selection["source_candidate_constraint_equation"]
        == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert (
        selection["source_admissibility_constraint_form"]
        == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selection["bridge_constraint_equation"] == "C_bridge^phi = 0"
    assert selection["bridge_admissibility_constraint_form"] == "C_bridge^phi = 0"
    assert selection["phi_ck_admissibility_rule_family_count"] == 2
    assert selection["closed_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
    ]
    assert selection["source_and_bridge_family_retained_as_context"] is True
    assert selection["source_admissibility_rule_retained_as_context"] is True
    assert selection["bridge_admissibility_rule_retained_as_context"] is True


def test_ck_constraint_family_selection_selects_transport_family() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert selection["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert selection["selected_family_selection_status"] == (
        "selected_as_next_ck_family_after_phi_source_and_bridge_admissibility"
    )
    assert selection["selector_target_prepared"] is True
    assert selection["selector_target_accepted"] is True
    assert selection["selection_executed"] is True
    assert selection["transport_consistency_family_selected"] is True
    assert selection["transport_consistency_candidate_packet_authorized"] is True
    assert selection["transport_consistency_candidate_packet_prepared"] is False
    assert selection["source_admissibility_family_reselected"] is False
    assert selection["bridge_admissibility_family_reselected"] is False


def test_ck_constraint_family_selection_records_transport_contract() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["transport_consistency_question"] == TRANSPORT_CONSISTENCY_QUESTION
    assert selection["transport_candidate_shape_preview"] == TRANSPORT_CANDIDATE_SHAPE_PREVIEW
    assert (
        selection["transport_candidate_plain_meaning"]
        == TRANSPORT_CANDIDATE_PLAIN_MEANING
    )
    assert selection["transport_chain_form"] == TRANSPORT_CHAIN_FORM
    assert selection["transport_chain_steps"] == TRANSPORT_CHAIN_STEPS
    assert selection["transport_chain_step_count"] == 7
    assert selection["transport_candidate_shape_preview_recorded"] is True
    assert selection["transport_chain_recorded"] is True
    assert selection["transport_candidate_functional_defined"] is False
    assert selection["transport_consistency_proved"] is False
    assert selection["selection_criteria_count"] == 10
    assert selection["selection_criteria_accepted_count"] == 10
    assert {row["row_id"] for row in selection["selection_criteria"]} == {
        "selector_consumes_phi_source_bridge_family_target",
        "source_bridge_family_closeout_accepted",
        "source_admissibility_rule_retained",
        "bridge_admissibility_rule_retained",
        "transport_consistency_family_selected",
        "transport_question_matches_next_layer",
        "transport_candidate_shape_only_previewed",
        "transport_chain_recorded_for_next_packet",
        "next_transport_candidate_packet_authorized",
        "no_transport_proof_variation_or_promotion",
    }


def test_ck_constraint_family_selection_blocks_shortcuts() -> None:
    selection = _json(DEFAULT_OUT)
    for key in [
        "transport_consistency_candidate_packet_prepared",
        "transport_candidate_functional_defined",
        "transport_candidate_functional_selected",
        "transport_proof_claimed",
        "transport_consistency_proved",
        "transport_chain_compatibility_proved",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "candidate_action_insertion_executed",
        "constraint_as_action_term_selected",
        "constraint_term_selected",
        "ck_action_embedding_claimed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_executed",
        "phi_variation_executed",
        "native_phi_derivation_claimed",
        "phi_generated_by_ck_claimed",
        "phi_generation_theorem_claimed",
        "native_generation_theorem_claimed",
        "v_phi_derivation_claimed",
        "derived_v_phi_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
        "source_admissibility_proved",
        "source_conservation_proved",
        "bridge_admissibility_proved",
        "bridge_route_alignment_verified",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert selection[key] is False, key
    assert "only chooses transport_consistency_ck_constraint_family" in (
        selection["non_claim_boundary"]
    )
    assert "does not prepare the transport candidate packet" in (
        selection["non_claim_boundary"]
    )
    assert "does not define C_transport^phi" in selection["non_claim_boundary"]
    assert "does not prove transport consistency" in selection["non_claim_boundary"]
    assert "does not execute C_k variation" in selection["non_claim_boundary"]
    assert "does not promote the master action" in selection["non_claim_boundary"]


def test_ck_constraint_family_selection_validation_policy() -> None:
    selection = _json(DEFAULT_OUT)
    policy = selection["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_ck_constraint_family_selection_rotates_to_transport_candidate_packet() -> None:
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
        "CKConstraintFamilySelectionAfterPhiSourceAndBridgeAdmissibility.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "CK_CONSTRAINT_FAMILY_SELECTION_AFTER_PHI_SOURCE_AND_BRIDGE_"
        "ADMISSIBILITY_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert consumed["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert consumed["transport_consistency_family_selected"] == "yes"
    assert consumed["transport_candidate_functional_defined"] == "no"
    assert consumed["transport_consistency_proved"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["transport_consistency_candidate_packet_authorized"] == "yes"
    assert active_row["transport_consistency_candidate_packet_prepared"] == "no"
    assert active_row["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert active_row["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert active_row["transport_candidate_shape_preview"] == (
        TRANSPORT_CANDIDATE_SHAPE_PREVIEW
    )
    assert active_row["transport_candidate_functional_defined"] == "no"
    assert active_row["transport_consistency_proved"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_ck_constraint_family_selection_mirrors() -> None:
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
        SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "CKConstraintFamilySelectionAfterPhiSourceAndBridgeAdmissibility",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_transport_consistency_ck_constraint_candidate_packet",
        SELECTED_CK_OPTION_CLASS,
        SELECTED_CK_CONSTRAINT_FAMILY,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "C_bridge^phi = 0",
        TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
        TRANSPORT_CHAIN_FORM,
        "does not define C_transport^phi",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "no QFT-GR closure",
        "NOT_RUN",
    ]:
        assert token in joined


def test_ck_constraint_family_selection_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_constraint_family_selection_after_phi_source_and_bridge_admissibility_gate.py"
    )
