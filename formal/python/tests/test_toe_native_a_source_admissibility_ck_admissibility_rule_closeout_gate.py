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
from formal.python.tools.toe_native_a_source_admissibility_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ARTIFACT_ID,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CLOSEOUT_RESULT,
    COMPONENT_PAIRING_FORM,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIRST_A_RULE_CLASSIFICATION,
    FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    FULL_TOEFORMAL_STATUS,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_RECOMMENDED_A_CK_FAMILY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    QUADRATIC_PENALTY_ACTION_FORM,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    WEAK_INTEGRATED_FORM,
    build_toe_native_a_source_admissibility_ck_admissibility_rule_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_source_admissibility_ck_admissibility_rule_closeout_report.py"
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
        if row.get("workstream_id") == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_a_source_ck_admissibility_rule_closeout_files_exist() -> None:
    for path in [
        FUNCTIONAL_EMBEDDING_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_source_ck_admissibility_rule_closeout_accepts_review() -> None:
    review = _json(FUNCTIONAL_EMBEDDING_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    assert review["review_result"] == FUNCTIONAL_EMBEDDING_REVIEW_RESULT
    assert closeout["artifact_id"] == ARTIFACT_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_a_source_admissibility_ck_admissibility_rule_closeout() == closeout


def test_a_source_ck_admissibility_rule_closeout_preserves_rule() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert (
        closeout["first_A_relevant_ck_admissibility_rule_candidate_classification"]
        == FIRST_A_RULE_CLASSIFICATION
    )
    assert closeout["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert closeout["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert closeout["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert closeout["admissibility_constraint_form"] == ADMISSIBILITY_CONSTRAINT_FORM
    assert closeout["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert closeout["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert closeout["component_pairing_form"] == COMPONENT_PAIRING_FORM
    assert closeout["weak_integrated_form"] == WEAK_INTEGRATED_FORM
    assert closeout["quadratic_penalty_action_form"] == QUADRATIC_PENALTY_ACTION_FORM
    assert closeout["gauge_group_policy"] == "U(1) / Abelian test route"
    assert closeout["vacuum_euler_lagrange_route"] == "nabla_mu F^{mu nu} = 0"
    assert closeout["on_shell_vacuum_conservation_identity"] == (
        "nabla_mu T_A^{mu nu} = 0"
    )


def test_a_source_ck_admissibility_rule_closeout_records_required_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 11
    assert closeout["closeout_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "functional_embedding_review_accepts_admissibility_only",
        "vacuum_gauge_source_rule_closed",
        "conservation_residual_form_preserved",
        "admissibility_condition_preserved",
        "vacuum_u1_route_context_preserved",
        "not_action_term_or_dynamical_law",
        "multiplier_and_penalty_routes_remain_blocked",
        "no_current_or_sourced_em_route",
        "no_new_conservation_or_source_proof",
        "no_closure_coupling_validation_or_promotion",
        "next_family_selector_authorized",
    }
    for key in [
        "admissibility_rule_closeout_prepared",
        "admissibility_rule_closeout_accepted",
        "first_A_relevant_ck_admissibility_rule_candidate_closed",
        "A_source_admissibility_rule_candidate_closed",
        "vacuum_gauge_source_rule_closed",
        "source_admissibility_rule_closed_as_vacuum_gauge_rule",
        "candidate_recorded_as_rule_only",
        "admissibility_only_route_selected",
        "constraint_as_admissibility_rule_selected",
        "lagrange_multiplier_route_blocked",
        "next_selector_authorized",
    ]:
        assert closeout[key] is True, key
    assert closeout["next_selector_prepared"] is False
    assert closeout["next_candidate_family_recommendation"] == NEXT_RECOMMENDED_A_CK_FAMILY
    assert closeout["next_candidate_family_selected"] is False
    assert closeout["A_bridge_admissibility_family_selected"] is False


def test_a_source_ck_admissibility_rule_closeout_blocks_shortcuts() -> None:
    closeout = _json(DEFAULT_OUT)
    for key in [
        "candidate_recorded_as_action_term",
        "candidate_recorded_as_new_physical_law",
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "quadratic_penalty_route_licensed",
        "constraint_multiplier_type_selected",
        "lambda_nu_domain_selected",
        "component_pairing_rule_selected",
        "variation_policy_selected",
        "higher_derivative_analysis_completed",
        "boundary_terms_controlled",
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
        "full_source_admissibility_review_accepted",
        "source_admissibility_completed",
        "A_source_admissibility_proved",
        "A_relevant_C_k_rules_constructed",
        "A_relevant_C_k_triads_constructed",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "canonical_master_action_promoted",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert closeout[key] is False, key
    for phrase in [
        "vacuum U(1) source-admissibility rule only",
        "not an action term",
        "not a dynamical law",
        "not a C_k variation",
        "not sourced Maxwell theory",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "A_bridge_admissibility_constraint_family is recommended only",
    ]:
        assert phrase in closeout["non_claim_boundary"], phrase


def test_a_source_ck_admissibility_rule_closeout_validation_policy_not_run() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["full_toeformal_aggregate_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_source_ck_admissibility_rule_closeout_rotates_to_selector() -> None:
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
        "ToeNativeASourceAdmissibilityCKAdmissibilityRuleCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_rule_closeout_prepared"] == "yes"
    assert consumed["vacuum_gauge_source_rule_closed"] == "yes"
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
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["next_selector_authorized"] == "yes"
    assert active_row["next_selector_prepared"] == "no"
    assert active_row["next_candidate_family_recommendation"] == NEXT_RECOMMENDED_A_CK_FAMILY
    assert active_row["next_candidate_family_selected"] == "no"
    assert active_row["A_bridge_admissibility_family_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_source_ck_admissibility_rule_closeout_mirrors() -> None:
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
        CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeASourceAdmissibilityCKAdmissibilityRuleCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_ck_constraint_family_after_source_admissibility",
        "HISTORICAL_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_"
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_source_admissibility_ck_admissibility_rule_closeout",
        CANDIDATE_CONSTRAINT_ID,
        CANDIDATE_CONSTRAINT_FORM,
        CANDIDATE_CONSTRAINT_EQUATION,
        ADMISSIBILITY_CONSTRAINT_FORM,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        QUADRATIC_PENALTY_ACTION_FORM,
        "vacuum U(1) admissibility-only source rule",
        "not an action term",
        "not a dynamical law",
        "not a C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "A_bridge_admissibility_constraint_family",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_source_ck_admissibility_rule_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_source_admissibility_ck_admissibility_rule_closeout_gate.py"
    )
