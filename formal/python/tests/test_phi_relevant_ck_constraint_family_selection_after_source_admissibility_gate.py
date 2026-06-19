from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_relevant_ck_constraint_family_selection_after_source_admissibility_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_QUESTION,
    BRIDGE_CANDIDATE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_SHAPE_PREVIEW,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
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
    PREVIOUS_CK_CONSTRAINT_FAMILY,
    PREVIOUS_CK_OPTION_CLASS,
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
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    SOURCE_RULE_CLOSEOUT_PATH,
    build_phi_relevant_ck_constraint_family_selection_after_source_admissibility,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_relevant_ck_constraint_family_selection_after_source_admissibility_report.py"
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


def test_phi_relevant_ck_constraint_family_selection_files_exist() -> None:
    for path in [
        SOURCE_RULE_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_relevant_ck_constraint_family_selection_accepts_source_closeout() -> None:
    closeout = _json(SOURCE_RULE_CLOSEOUT_PATH)
    selection = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == SOURCE_RULE_CLOSEOUT_OUTCOME
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
        build_phi_relevant_ck_constraint_family_selection_after_source_admissibility()
        == selection
    )


def test_phi_relevant_ck_constraint_family_selection_selects_bridge_family() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["source_selected_ck_option_class"] == PREVIOUS_CK_OPTION_CLASS
    assert (
        selection["source_selected_ck_constraint_family"]
        == PREVIOUS_CK_CONSTRAINT_FAMILY
    )
    assert selection["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert selection["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert selection["selected_family_selection_status"] == (
        "selected_as_next_abstract_phi_relevant_family"
    )
    assert selection["selector_target_prepared"] is True
    assert selection["selector_target_accepted"] is True
    assert selection["selection_executed"] is True
    assert selection["bridge_admissibility_family_selected"] is True
    assert selection["bridge_admissibility_recommended_only"] is False
    assert selection["bridge_admissibility_candidate_packet_authorized"] is True
    assert selection["bridge_admissibility_candidate_packet_prepared"] is False
    assert selection["source_admissibility_family_reselected"] is False


def test_phi_relevant_ck_constraint_family_selection_preserves_source_rule_context() -> None:
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
    assert selection["source_family_status"] == (
        "closed_as_first_rule_candidate_reference_not_reselected"
    )
    assert selection["source_admissibility_family_completed"] is False
    assert selection["source_admissibility_family_closed_as_candidate_only"] is True
    assert selection["source_rule_candidate_retained_as_context"] is True


def test_phi_relevant_ck_constraint_family_selection_records_bridge_packet_contract() -> None:
    selection = _json(DEFAULT_OUT)
    assert selection["bridge_admissibility_question"] == BRIDGE_ADMISSIBILITY_QUESTION
    assert selection["bridge_candidate_shape_preview"] == BRIDGE_CANDIDATE_SHAPE_PREVIEW
    assert selection["bridge_candidate_plain_meaning"] == BRIDGE_CANDIDATE_PLAIN_MEANING
    assert selection["bridge_route_alignment_sequence"] == BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
    assert selection["bridge_route_alignment_sequence_count"] == 7
    assert selection["bridge_candidate_shape_preview_recorded"] is True
    assert selection["bridge_candidate_functional_defined"] is False
    assert selection["bridge_route_alignment_sequence_recorded"] is True
    assert selection["bridge_route_alignment_verified"] is False
    assert selection["candidate_family_option_count"] == 2
    assert selection["selection_criteria_count"] == 10
    assert selection["selection_criteria_accepted_count"] == 10
    assert {row["row_id"] for row in selection["selection_criteria"]} == {
        "selector_consumes_authorized_target",
        "source_admissibility_rule_closeout_accepted",
        "source_admissibility_not_reselected",
        "bridge_family_selected_as_next_phi_relevant_family",
        "bridge_question_matches_next_seam_layer",
        "bridge_candidate_shape_only_previewed",
        "route_alignment_sequence_recorded_for_next_packet",
        "next_candidate_packet_authorized",
        "no_candidate_functional_or_variation",
        "no_generation_closure_or_promotion",
    }


def test_phi_relevant_ck_constraint_family_selection_blocks_shortcuts() -> None:
    selection = _json(DEFAULT_OUT)
    for key in [
        "bridge_candidate_functional_defined",
        "bridge_candidate_functional_selected",
        "bridge_candidate_rule_proved",
        "bridge_route_alignment_verified",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "candidate_action_insertion_executed",
        "ck_action_embedding_claimed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "lambda_nu_domain_selected",
        "higher_derivative_scope_resolved",
        "boundary_terms_controlled",
        "phi_generated_by_ck_claimed",
        "phi_generation_theorem_claimed",
        "native_generation_theorem_claimed",
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "bridge_admissibility_claimed",
        "bridge_admissibility_proved",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
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
    assert "only chooses the phi bridge-admissibility C_k family" in (
        selection["non_claim_boundary"]
    )
    assert "does not define C_bridge^phi" in selection["non_claim_boundary"]
    assert "does not prove bridge admissibility" in selection["non_claim_boundary"]
    assert "does not execute C_k variation" in selection["non_claim_boundary"]
    assert "does not promote the master action" in selection["non_claim_boundary"]


def test_phi_relevant_ck_constraint_family_selection_validation_policy() -> None:
    selection = _json(DEFAULT_OUT)
    policy = selection["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_relevant_ck_constraint_family_selection_rotates_to_bridge_candidate() -> None:
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
        "PhiRelevantCKConstraintFamilySelectionAfterSourceAdmissibility.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_RELEVANT_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_ADMISSIBILITY_"
        "20260618_v0.json"
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
    assert consumed["bridge_admissibility_family_selected"] == "yes"
    assert consumed["bridge_candidate_functional_defined"] == "no"
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
    assert active_row["bridge_admissibility_candidate_packet_authorized"] == "yes"
    assert active_row["bridge_admissibility_candidate_packet_prepared"] == "no"
    assert active_row["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert active_row["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert active_row["bridge_candidate_shape_preview"] == BRIDGE_CANDIDATE_SHAPE_PREVIEW
    assert active_row["bridge_candidate_functional_defined"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["bridge_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_relevant_ck_constraint_family_selection_mirrors() -> None:
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
        "PhiRelevantCKConstraintFamilySelectionAfterSourceAdmissibility",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_bridge_admissibility_ck_constraint_candidate_packet",
        SELECTED_CK_OPTION_CLASS,
        SELECTED_CK_CONSTRAINT_FAMILY,
        BRIDGE_CANDIDATE_SHAPE_PREVIEW,
        "master-action phi surface",
        "source-admissibility rule",
        "does not define C_bridge^phi",
        "does not execute C_k variation",
        "does not prove bridge admissibility",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_phi_relevant_ck_constraint_family_selection_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_relevant_ck_constraint_family_selection_after_source_admissibility_gate.py"
    )
