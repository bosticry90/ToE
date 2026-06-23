from __future__ import annotations

import json
import sys
from pathlib import Path

sys.setrecursionlimit(10000)

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_source_admissibility_ck_constraint_candidate_packet_report import (
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
)
from formal.python.tools.toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review_report import (
    ARTIFACT_ID,
    CANDIDATE_ACTION_INSERTION_FORM,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CANDIDATE_CONSTRAINT_SHORT_FORM,
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
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
    build_toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review_report.py"
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


def test_a_source_admissibility_ck_candidate_review_files_exist() -> None:
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


def test_a_source_admissibility_ck_candidate_review_accepts_residual_candidate() -> None:
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
        build_toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review()
        == review
    )


def test_a_source_admissibility_ck_candidate_review_carries_forms_exactly() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert review["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert review["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert review["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert review["candidate_constraint_short_form"] == CANDIDATE_CONSTRAINT_SHORT_FORM
    assert review["candidate_action_insertion_form"] == CANDIDATE_ACTION_INSERTION_FORM
    assert review["vacuum_supporting_identity_form"] == VACUUM_SUPPORTING_IDENTITY_FORM
    assert review["vacuum_on_shell_implication_form"] == VACUUM_ON_SHELL_IMPLICATION_FORM
    assert review["review_accepts_vacuum_gauge_conservation_residual_candidate"] is True
    assert review["candidate_recorded_as_candidate_only"] is True
    assert review["candidate_carried_forward_exactly"] is True
    assert review["vacuum_u1_scope_preserved"] is True
    assert review["accepted_vacuum_source_route_retained_as_context"] is True
    assert review["admissibility_only_interpretation_retained"] is True
    assert review["dynamical_action_embedding_not_assumed"] is True


def test_a_source_admissibility_ck_candidate_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 11
    assert review["review_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "candidate_review_target_consumed",
        "vacuum_conservation_residual_form_carried_forward",
        "vacuum_conservation_residual_equation_carried_forward",
        "vacuum_u1_scope_preserved",
        "accepted_vacuum_source_route_retained_as_context",
        "admissibility_only_candidate_retained",
        "candidate_action_insertion_not_functionalized",
        "no_ck_variation_executed",
        "no_current_or_sourced_maxwell_route",
        "no_closure_coupling_validation_or_promotion",
        "functional_embedding_next_target_selected",
    }


def test_a_source_admissibility_ck_candidate_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["functional_embedding_packet_authorized"] is True
    assert review["functional_embedding_packet_prepared"] is False
    for key in [
        "functional_embedding_executed",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "lambda_nu_domain_selected",
        "higher_derivative_scope_resolved",
        "boundary_terms_controlled",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "ck_functional_formula_fully_defined",
        "ck_functional_formula_selected",
        "candidate_action_insertion_executed",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "canonical_master_action_promoted",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    assert "accepts the vacuum gauge conservation-residual candidate only" in (
        review["non_claim_boundary"]
    )
    assert "does not functionalize the candidate" in review["non_claim_boundary"]
    assert "does not embed it in S_C" in review["non_claim_boundary"]
    assert "does not execute C_k variation" in review["non_claim_boundary"]
    assert "does not derive J^nu" in review["non_claim_boundary"]
    assert "does not derive sourced Maxwell" in review["non_claim_boundary"]
    assert "does not close EM" in review["non_claim_boundary"]
    assert "does not close QFT-GR" in review["non_claim_boundary"]


def test_a_source_admissibility_ck_candidate_review_validation_policy_not_run() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_a_source_admissibility_ck_candidate_review_rotates_to_embedding_target() -> None:
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
        "ToeNativeASourceAdmissibilityCKConstraintCandidatePacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
        "RESULT_REVIEW_20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert consumed["review_accepts_vacuum_gauge_conservation_residual_candidate"] == "yes"
    assert consumed["functional_embedding_packet_authorized"] == "yes"
    assert consumed["functional_embedding_executed"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["functional_embedding_packet_authorized"] == "yes"
    assert active_row["functional_embedding_packet_prepared"] == "no"
    assert active_row["admissibility_only_interpretation_retained"] == "yes"
    assert active_row["dynamical_action_embedding_not_assumed"] == "yes"
    assert active_row["constraint_multiplier_type_selected"] == "no"
    assert active_row["constraint_term_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_current_exchange_route_proved"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_source_admissibility_ck_candidate_review_mirrors() -> None:
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
        "ToeNativeASourceAdmissibilityCKConstraintCandidatePacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_source_admissibility_ck_functional_embedding_packet",
        CANDIDATE_CONSTRAINT_ID,
        CANDIDATE_CONSTRAINT_FORM,
        CANDIDATE_CONSTRAINT_EQUATION,
        "accepts the vacuum gauge conservation-residual candidate only",
        "does not functionalize the candidate",
        "does not embed it in S_C",
        "admissibility-only interpretation",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_source_admissibility_ck_candidate_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review_gate.py"
    )
