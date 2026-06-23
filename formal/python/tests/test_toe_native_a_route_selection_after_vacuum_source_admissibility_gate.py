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
    A_SOURCE_CK_RULE_CANDIDATE,
    A_SOURCE_CK_RULE_CLASSIFICATION,
    A_SOURCE_CK_RULE_INTERPRETATION,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIVERGENCE_IDENTITY,
    GAUGE_GROUP_POLICY,
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
    ROUTE_SELECTOR_CANDIDATES,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_ROUTE_ID,
    SELECTED_ROUTE_LABEL,
    SELECTION_RESULT,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_route_selection_after_vacuum_source_admissibility,
)
from formal.python.tools.toe_native_a_source_admissibility_review_retry_after_vacuum_identity_result_review_report import (
    DEFAULT_OUT as A_SOURCE_RETRY_RESULT_REVIEW_PATH,
    OUTCOME_ID as A_SOURCE_RETRY_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_route_selection_after_vacuum_source_admissibility_report.py"
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


def test_a_route_selection_after_vacuum_source_admissibility_files_exist() -> None:
    for path in [
        A_SOURCE_RETRY_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_route_selection_after_vacuum_source_admissibility_selects_ck_candidate() -> None:
    review = _json(A_SOURCE_RETRY_RESULT_REVIEW_PATH)
    selector = _json(DEFAULT_OUT)
    assert review["outcome_id"] == A_SOURCE_RETRY_RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET
    assert selector["artifact_id"] == ARTIFACT_ID
    assert selector["schema_id"] == SCHEMA_ID
    assert selector["packet_id"] == PACKET_ID
    assert selector["prepared"] is True
    assert selector["accepted"] is True
    assert selector["packet_result"] == "SELECTED"
    assert selector["outcome_id"] == OUTCOME_ID
    assert selector["selection_result"] == SELECTION_RESULT
    assert selector["route_selection_result"] == SELECTION_RESULT
    assert selector["packet_classification"] == PACKET_CLASSIFICATION
    assert selector["consumed_target"] == CONSUMED_TARGET
    assert selector["selected_next_target"] == NEXT_TARGET
    assert selector["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert selector["selected_route_id"] == SELECTED_ROUTE_ID
    assert selector["selected_route_label"] == SELECTED_ROUTE_LABEL
    assert selector["selected_route_status"] == "selected_for_packet_preparation"
    assert selector["selected_route_execution_status"] == "not_executed"
    assert selector["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert build_toe_native_a_route_selection_after_vacuum_source_admissibility() == selector


def test_a_route_selection_after_vacuum_source_admissibility_records_rule_candidate() -> None:
    selector = _json(DEFAULT_OUT)
    assert selector["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert selector["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert selector["stress_energy_under_selected_u1_policy"] == (
        STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
    )
    assert selector["divergence_identity"] == DIVERGENCE_IDENTITY
    assert selector["source_rule_candidate"] == A_SOURCE_CK_RULE_CANDIDATE
    assert selector["A_source_ck_rule_candidate"] == A_SOURCE_CK_RULE_CANDIDATE
    assert selector["source_rule_candidate_short_form"] == (
        "C_source^A := nabla_mu T_A^{mu nu}; C_source^A = 0"
    )
    assert selector["source_rule_candidate_interpretation"] == (
        A_SOURCE_CK_RULE_INTERPRETATION
    )
    assert selector["source_rule_candidate_classification"] == (
        A_SOURCE_CK_RULE_CLASSIFICATION
    )
    assert selector["route_selector_candidates"] == ROUTE_SELECTOR_CANDIDATES
    assert selector["route_option_count"] == 6
    assert selector["route_options_selected_count"] == 1
    assert selector["route_options_deferred_count"] == 5
    assert selector["selection_criteria_count"] == 12
    assert selector["selection_criteria_accepted_count"] == 12
    statuses = {row["route_id"]: row["status"] for row in selector["route_options"]}
    assert statuses == {
        "A_source_admissibility_C_k_constraint_candidate": (
            "selected_for_packet_preparation"
        ),
        "A_current_coupling_policy": "deferred_blocked_pending_J_nu_policy",
        "A_current_conservation_route": (
            "deferred_blocked_without_sourced_maxwell_or_exchange_route"
        ),
        "A_bridge_admissibility_C_k_constraint_candidate": (
            "deferred_until_A_source_ck_candidate_recorded"
        ),
        "A_transport_consistency_C_k_constraint_candidate": (
            "deferred_until_A_source_and_bridge_ck_candidates_exist"
        ),
        "A_full_EM_closure": "blocked_out_of_scope_for_bounded_vacuum_route",
    }


def test_a_route_selection_after_vacuum_source_admissibility_blocks_promotions() -> None:
    selector = _json(DEFAULT_OUT)
    for key in [
        "selector_prepared",
        "selector_executed",
        "route_selection_executed",
        "next_a_route_selected",
        "A_relevant_C_k_route_selected",
        "A_relevant_C_k_candidate_packet_selected",
        "A_source_admissibility_C_k_candidate_selected",
        "source_admissibility_ck_constraint_candidate_packet_selected",
        "source_admissibility_ck_candidate_packet_authorized",
        "source_rule_candidate_recorded_for_next_packet",
        "candidate_packet_authorized",
    ]:
        assert selector[key] is True, key
    for key in [
        "source_admissibility_ck_candidate_packet_prepared",
        "candidate_packet_prepared",
        "candidate_packet_executed",
        "source_rule_candidate_promoted_to_action_term",
        "source_rule_candidate_promoted_to_dynamical_law",
        "source_rule_candidate_treated_as_sourced_em",
        "source_rule_candidate_treated_as_em_closure",
        "ck_action_embedding_selected",
        "ck_action_embedding_constructed",
        "ck_variation_executed",
        "A_relevant_C_k_rules_constructed",
        "A_source_C_k_rule_constructed",
        "source_bridge_transport_ck_analogues_constructed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "full_em_closure_claimed",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert selector[key] is False, key
    for phrase in [
        "selects only the next A source-admissibility C_k constraint candidate packet",
        "does not prepare the candidate packet",
        "does not embed C_k in the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not construct A-relevant C_k rules",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in selector["non_claim_boundary"], phrase


def test_a_route_selection_after_vacuum_source_admissibility_rotates_live_target() -> None:
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
        "ToeNativeARouteSelectionAfterVacuumSourceAdmissibility.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == "SELECTED"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["source_rule_candidate"] == A_SOURCE_CK_RULE_CANDIDATE
    assert consumed["source_rule_candidate_recorded_for_next_packet"] == "yes"
    assert consumed["source_admissibility_ck_candidate_packet_prepared"] == "no"
    assert consumed["A_relevant_C_k_route_selected"] == "yes"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["ck_action_embedding_constructed"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["matter_gauge_energy_exchange_proved"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["packet_result"] == "PENDING"
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["source_rule_candidate"] == A_SOURCE_CK_RULE_CANDIDATE
    assert active_row["source_rule_candidate_recorded_for_next_packet"] == "yes"
    assert active_row["source_admissibility_ck_candidate_packet_prepared"] == "no"
    assert active_row["A_relevant_C_k_route_selected"] == "yes"
    assert active_row["A_relevant_C_k_rules_constructed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_route_selection_after_vacuum_source_admissibility_mirrors() -> None:
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
        SELECTED_ROUTE_ID,
        SELECTED_A_CK_CONSTRAINT_FAMILY,
        A_SOURCE_CK_RULE_CANDIDATE,
        "ToeNativeARouteSelectionAfterVacuumSourceAdmissibility",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_source_admissibility_ck_constraint_candidate_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_route_after_vacuum_source_admissibility",
        "HISTORICAL_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_VACUUM_SOURCE_ADMISSIBILITY_CURRENT_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_route_after_vacuum_source_admissibility",
        "not an action term",
        "not sourced Maxwell theory",
        "does not embed C_k in the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not close QFT-GR",
        "master action",
    ]:
        assert token in joined


def test_a_route_selection_after_vacuum_source_admissibility_validation_policy_is_bounded() -> None:
    selector = _json(DEFAULT_OUT)
    policy = selector["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS"
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["full_toeformal_aggregate_status_for_packet"] == (
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS"
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is True


def test_a_route_selection_after_vacuum_source_admissibility_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_route_selection_after_vacuum_source_admissibility_gate.py"
    )
