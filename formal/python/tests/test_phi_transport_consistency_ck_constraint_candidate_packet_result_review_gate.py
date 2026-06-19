from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_transport_consistency_ck_constraint_candidate_packet_report import (
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
)
from formal.python.tools.phi_transport_consistency_ck_constraint_candidate_packet_result_review_report import (
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
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
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_phi_transport_consistency_ck_constraint_candidate_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_consistency_ck_constraint_candidate_packet_result_review_report.py"
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


def test_phi_transport_consistency_ck_candidate_review_files_exist() -> None:
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


def test_phi_transport_consistency_ck_candidate_review_accepts_candidate() -> None:
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
        build_phi_transport_consistency_ck_constraint_candidate_packet_result_review()
        == review
    )


def test_phi_transport_consistency_ck_candidate_review_preserves_transport_rule() -> None:
    review = _json(DEFAULT_OUT)
    assert review["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert review["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert review["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert review["transport_rule_epistemic_status"] == TRANSPORT_RULE_EPISTEMIC_STATUS
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert review["known_phi_transport_chain_form"] == KNOWN_PHI_TRANSPORT_CHAIN_FORM
    assert review["transport_constraint_preserved"] is True
    assert review["transport_tuple_preserved"] is True
    assert review["transport_components_preserved"] is True
    assert review["transport_components_proved"] is False
    assert review["transport_candidate_classified_as_admissibility_only"] is True
    assert review["review_accepts_derivation_chain_stability_candidate"] is True
    assert review["derivation_chain_stability_candidate_accepted"] is True


def test_phi_transport_consistency_ck_candidate_review_preserves_context() -> None:
    review = _json(DEFAULT_OUT)
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
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["closed_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert review["phi_ck_rule_family_count_after_review"] == 3
    assert review["source_and_bridge_context_retained"] is True
    assert review["known_phi_chain_retained"] is True


def test_phi_transport_consistency_ck_candidate_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["functional_embedding_packet_authorized"] is True
    assert review["functional_embedding_packet_prepared"] is False
    assert review["multiplier_action_route_test_authorized"] is True
    assert review["penalty_route_test_authorized"] is True
    assert review["direct_dynamical_law_interpretation_test_authorized"] is True
    for key in [
        "functional_embedding_executed",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_interpretation_selected",
        "transport_candidate_functional_defined",
        "transport_candidate_functional_selected",
        "transport_candidate_recorded_as_action_term",
        "transport_candidate_recorded_as_new_dynamical_law",
        "transport_candidate_rule_proved",
        "transport_consistency_claimed",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "full_route_alignment_proof_claimed",
        "full_route_alignment_proved",
        "route_chain_compatibility_proved",
        "source_admissibility_proved",
        "bridge_admissibility_proved",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "ck_action_embedding_claimed",
        "candidate_action_insertion_executed",
        "constraint_as_action_term_selected",
        "constraint_term_selected",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "native_phi_derivation_claimed",
        "phi_generated_by_ck_claimed",
        "v_phi_derivation_claimed",
        "derived_v_phi_claimed",
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
    assert "does not functionalize C_transport^phi" in review["non_claim_boundary"]
    assert "does not embed it in S_C" in review["non_claim_boundary"]
    assert "does not define a C_k action term" in review["non_claim_boundary"]
    assert "does not select a multiplier/action route" in review["non_claim_boundary"]
    assert "does not prove transport consistency" in review["non_claim_boundary"]
    assert "does not prove full route alignment" in review["non_claim_boundary"]
    assert "does not promote the master action" in review["non_claim_boundary"]


def test_phi_transport_consistency_ck_candidate_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_phi_transport_consistency_ck_candidate_review_rotates_to_embedding() -> None:
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
        "PhiTransportConsistencyCKConstraintCandidatePacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
        "20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert consumed["review_accepts_derivation_chain_stability_candidate"] == "yes"
    assert consumed["functional_embedding_packet_authorized"] == "yes"
    assert consumed["functional_embedding_packet_prepared"] == "no"
    assert consumed["transport_candidate_functional_defined"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["functional_embedding_packet_authorized"] == "yes"
    assert active_row["functional_embedding_packet_prepared"] == "no"
    assert active_row["multiplier_action_route_test_authorized"] == "yes"
    assert active_row["penalty_route_test_authorized"] == "yes"
    assert active_row["direct_dynamical_law_interpretation_test_authorized"] == "yes"
    assert active_row["multiplier_action_route_selected"] == "no"
    assert active_row["penalty_route_selected"] == "no"
    assert active_row["direct_dynamical_law_interpretation_selected"] == "no"
    assert active_row["transport_candidate_functional_defined"] == "no"
    assert active_row["ck_action_embedding_claimed"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_transport_consistency_ck_candidate_review_mirrors() -> None:
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
        "PhiTransportConsistencyCKConstraintCandidatePacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_transport_consistency_ck_functional_embedding_packet",
        TRANSPORT_CANDIDATE_ID,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        SOURCE_CANDIDATE_CONSTRAINT_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        "admissibility-only derivation-chain stability candidate",
        "does not functionalize C_transport^phi",
        "does not embed it in S_C",
        "does not define a C_k action term",
        "does not prove transport consistency",
        "does not prove full route alignment",
        "does not close QFT-GR",
        "does not promote the master action",
        "NOT_RUN",
    ]:
        assert token in joined


def test_phi_transport_consistency_ck_candidate_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_consistency_ck_constraint_candidate_packet_result_review_gate.py"
    )
