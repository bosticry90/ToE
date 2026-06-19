from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_bridge_admissibility_ck_constraint_candidate_packet_report import (
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
)
from formal.python.tools.phi_bridge_admissibility_ck_constraint_candidate_packet_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
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
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    build_phi_bridge_admissibility_ck_constraint_candidate_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_bridge_admissibility_ck_constraint_candidate_packet_result_review_report.py"
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


def test_phi_bridge_admissibility_ck_candidate_review_files_exist() -> None:
    for path in [
        CANDIDATE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_bridge_admissibility_ck_candidate_review_accepts_route_candidate() -> None:
    packet = _json(CANDIDATE_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == CANDIDATE_PACKET_OUTCOME
    assert packet["packet_result"] == CANDIDATE_PACKET_RESULT
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["candidate_packet_outcome"] == CANDIDATE_PACKET_OUTCOME
    assert review["candidate_packet_result"] == CANDIDATE_PACKET_RESULT
    assert (
        build_phi_bridge_admissibility_ck_constraint_candidate_packet_result_review()
        == review
    )


def test_phi_bridge_admissibility_ck_candidate_review_carries_tuple_exactly() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert review["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert review["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert review["bridge_candidate_type"] == BRIDGE_CANDIDATE_TYPE
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert (
        review["bridge_route_field_equation_match"]
        == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert (
        review["bridge_route_stress_energy_match"]
        == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert (
        review["bridge_route_source_residual_match"]
        == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )
    assert review["bridge_candidate_rule_plain_meaning"] == (
        BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
    )
    assert review["bridge_component_count"] == 3
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert (
        review["source_candidate_constraint_equation"]
        == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert (
        review["source_admissibility_constraint_form"]
        == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )


def test_phi_bridge_admissibility_ck_candidate_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 12
    assert review["review_criteria_accepted_count"] == 12
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "bridge_candidate_recorded_as_candidate_only",
        "route_consistency_tuple_carried_forward_exactly",
        "bridge_condition_carried_forward_exactly",
        "field_equation_match_component_preserved",
        "stress_energy_match_component_preserved",
        "source_residual_match_component_preserved",
        "source_admissibility_context_preserved",
        "no_bridge_functionalization",
        "no_ck_variation_or_action_embedding",
        "no_bridge_proof_or_route_verification",
        "no_generation_potential_closure_or_promotion",
        "functional_embedding_next_target_selected",
    }
    assert review["review_accepts_route_consistency_candidate"] is True
    assert review["route_consistency_candidate_accepted"] is True
    assert review["bridge_candidate_recorded_as_candidate_only"] is True
    assert review["route_consistency_tuple_carried_forward"] is True
    assert review["field_equation_match_component_preserved"] is True
    assert review["stress_energy_match_component_preserved"] is True
    assert review["source_residual_match_component_preserved"] is True


def test_phi_bridge_admissibility_ck_candidate_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["functional_embedding_packet_authorized"] is True
    assert review["functional_embedding_packet_prepared"] is False
    for key in [
        "functional_embedding_executed",
        "bridge_functional_selected",
        "bridge_candidate_functional_defined",
        "bridge_candidate_functional_selected",
        "bridge_candidate_recorded_as_action_term",
        "bridge_candidate_recorded_as_new_dynamical_law",
        "bridge_candidate_rule_proved",
        "bridge_admissibility_claimed",
        "bridge_admissibility_proved",
        "bridge_route_alignment_verified",
        "route_consistency_tuple_proved",
        "field_equation_match_proved",
        "stress_energy_match_proved",
        "source_residual_match_proved",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "ck_action_embedding_claimed",
        "candidate_action_insertion_executed",
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
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "source_admissibility_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "master_action_promoted",
        "canonical_master_action_promoted",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    assert "accepts the route-consistency candidate only" in (
        review["non_claim_boundary"]
    )
    assert "does not functionalize C_bridge^phi" in review["non_claim_boundary"]
    assert "does not embed it in S_C" in review["non_claim_boundary"]
    assert "does not define a C_k action term" in review["non_claim_boundary"]
    assert "does not verify the full route alignment" in review["non_claim_boundary"]
    assert "does not claim full bridge admissibility" in review["non_claim_boundary"]
    assert "does not promote the master action" in review["non_claim_boundary"]


def test_phi_bridge_admissibility_ck_candidate_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_bridge_admissibility_ck_candidate_review_rotates_to_embedding_target() -> None:
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
        "PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_BRIDGE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
        "20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert consumed["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert consumed["review_accepts_route_consistency_candidate"] == "yes"
    assert consumed["functional_embedding_packet_authorized"] == "yes"
    assert consumed["functional_embedding_executed"] == "no"
    assert consumed["bridge_candidate_functional_defined"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["functional_embedding_packet_authorized"] == "yes"
    assert active_row["functional_embedding_packet_prepared"] == "no"
    assert active_row["route_consistency_candidate_accepted"] == "yes"
    assert active_row["field_equation_match_component_preserved"] == "yes"
    assert active_row["stress_energy_match_component_preserved"] == "yes"
    assert active_row["source_residual_match_component_preserved"] == "yes"
    assert active_row["bridge_candidate_functional_defined"] == "no"
    assert active_row["ck_action_embedding_claimed"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_bridge_admissibility_ck_candidate_review_mirrors() -> None:
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
        "PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_bridge_admissibility_ck_functional_embedding_packet",
        BRIDGE_CANDIDATE_ID,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "accepts the route-consistency candidate only",
        "does not functionalize C_bridge^phi",
        "does not embed it in S_C",
        "does not define a C_k action term",
        "does not verify the full route alignment",
        "does not claim full bridge admissibility",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_phi_bridge_admissibility_ck_candidate_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_bridge_admissibility_ck_constraint_candidate_packet_result_review_gate.py"
    )
