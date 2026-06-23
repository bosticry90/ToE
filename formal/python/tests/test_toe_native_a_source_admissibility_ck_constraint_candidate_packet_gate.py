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
from formal.python.tools.toe_native_a_route_selection_after_vacuum_source_admissibility_report import (
    DEFAULT_OUT as A_ROUTE_SELECTION_PATH,
    OUTCOME_ID as A_ROUTE_SELECTION_OUTCOME,
)
from formal.python.tools.toe_native_a_source_admissibility_ck_constraint_candidate_packet_report import (
    ARTIFACT_ID,
    CANDIDATE_ACTION_INSERTION_FORM,
    CANDIDATE_CONSTRAINT_CLASSIFICATION,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CANDIDATE_CONSTRAINT_INTERPRETATION,
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
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_SCOPE,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
    VACUUM_SUPPORTING_IDENTITY_ID,
    build_toe_native_a_source_admissibility_ck_constraint_candidate_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_source_admissibility_ck_constraint_candidate_packet_report.py"
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


def test_a_source_admissibility_ck_candidate_files_exist() -> None:
    for path in [
        A_ROUTE_SELECTION_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_source_admissibility_ck_candidate_records_vacuum_residual() -> None:
    selector = _json(A_ROUTE_SELECTION_PATH)
    packet = _json(DEFAULT_OUT)
    assert selector["outcome_id"] == A_ROUTE_SELECTION_OUTCOME
    assert selector["selected_next_target"] == CONSUMED_TARGET
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert packet["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert packet["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert packet["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert packet["candidate_constraint_short_form"] == CANDIDATE_CONSTRAINT_SHORT_FORM
    assert packet["candidate_constraint_interpretation"] == (
        CANDIDATE_CONSTRAINT_INTERPRETATION
    )
    assert packet["candidate_constraint_classification"] == (
        CANDIDATE_CONSTRAINT_CLASSIFICATION
    )
    assert packet["rule_scope"] == RULE_SCOPE
    assert packet["vacuum_supporting_identity_id"] == VACUUM_SUPPORTING_IDENTITY_ID
    assert packet["vacuum_supporting_identity_form"] == VACUUM_SUPPORTING_IDENTITY_FORM
    assert packet["vacuum_on_shell_implication_form"] == (
        VACUUM_ON_SHELL_IMPLICATION_FORM
    )
    assert packet["candidate_action_insertion_form"] == CANDIDATE_ACTION_INSERTION_FORM
    assert build_toe_native_a_source_admissibility_ck_constraint_candidate_packet() == (
        packet
    )


def test_a_source_admissibility_ck_candidate_options_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_shape_count"] == 2
    assert packet["candidate_shape_selected_count"] == 1
    assert packet["candidate_shape_supporting_count"] == 1
    shapes = {row["candidate_type"]: row for row in packet["candidate_shapes"]}
    assert shapes["vacuum_conservation_residual_constraint"][
        "selection_status"
    ] == "selected_as_first_A_source_candidate_shape"
    assert shapes["vacuum_on_shell_supporting_identity"]["selection_status"] == (
        "recorded_as_supporting_route_identity"
    )
    assert packet["review_row_count"] == 10
    assert packet["review_row_accepted_count"] == 10
    assert {row["row_id"] for row in packet["review_rows"]} == {
        "consumes_expected_candidate_packet_target",
        "selected_A_source_ck_family_carried_forward",
        "vacuum_u1_policy_preserved",
        "bounded_vacuum_route_preserved",
        "candidate_residual_recorded",
        "supporting_identity_recorded",
        "candidate_classified_as_admissibility_only",
        "candidate_action_insertion_not_executed",
        "current_routes_blocked",
        "no_closure_promotion_or_empirical_claim",
    }


def test_a_source_admissibility_ck_candidate_blocks_current_closure_and_promotion() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "candidate_packet_prepared",
        "candidate_constraint_shape_recorded",
        "vacuum_conservation_residual_candidate_selected",
        "source_admissibility_rule_candidate_recorded",
        "on_shell_vacuum_supporting_identity_recorded",
        "candidate_constraint_is_admissibility_only",
        "A_relevant_C_k_rule_candidate_recorded",
        "candidate_uses_accepted_vacuum_source_route",
        "candidate_uses_selected_u1_policy",
    ]:
        assert packet[key] is True, key
    for key in [
        "ck_action_embedding_selected",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_selected",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "source_rule_candidate_promoted_to_action_term",
        "source_rule_candidate_promoted_to_dynamical_law",
        "source_rule_candidate_treated_as_sourced_em",
        "source_rule_candidate_treated_as_em_closure",
        "J_nu_derived",
        "matter_current_J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "full_em_closure_claimed",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "canonical_master_action_promoted",
        "A_relevant_C_k_rules_constructed",
        "A_relevant_C_k_triads_constructed",
        "A_source_C_k_rule_constructed",
        "source_bridge_transport_ck_analogues_constructed",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "records only an A source-admissibility C_k candidate shape",
        "does not embed C_k in the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive a psi-current or external-current native route",
        "does not derive sourced Maxwell",
        "does not prove matter-current or matter-gauge exchange",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_source_admissibility_ck_candidate_validation_policy_not_run() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_source_admissibility_ck_candidate_rotates_to_review_target() -> None:
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
        "ToeNativeASourceAdmissibilityCKConstraintCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert consumed["candidate_constraint_shape_recorded"] == "yes"
    assert consumed["source_admissibility_rule_candidate_recorded"] == "yes"
    assert consumed["A_relevant_C_k_rule_candidate_recorded"] == "yes"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["ck_action_embedding_constructed"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["candidate_constraint_shape_recorded"] == "yes"
    assert active_row["review_prepared"] == "no"
    assert active_row["review_executed"] == "no"
    assert active_row["ck_action_embedding_constructed"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_current_exchange_route_proved"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_source_admissibility_ck_candidate_mirrors() -> None:
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
        PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeASourceAdmissibilityCKConstraintCandidatePacket",
        "HISTORICAL_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_"
        "PACKET_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet",
        "HISTORICAL_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_"
        "PACKET_RESULT_REVIEW_CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_source_admissibility_ck_constraint_candidate_packet_result",
        CANDIDATE_CONSTRAINT_ID,
        CANDIDATE_CONSTRAINT_FORM,
        CANDIDATE_CONSTRAINT_EQUATION,
        VACUUM_SUPPORTING_IDENTITY_FORM,
        VACUUM_ON_SHELL_IMPLICATION_FORM,
        "vacuum U(1) admissibility-only source-rule candidate",
        "does not embed C_k in the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_source_admissibility_ck_candidate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_source_admissibility_ck_constraint_candidate_packet_gate.py"
    )
