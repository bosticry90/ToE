from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_stress_energy_route_under_selected_u1_policy_packet_report import (
    DEFAULT_OUT as A_STRESS_ENERGY_PACKET_PATH,
    OUTCOME_ID as A_STRESS_ENERGY_PACKET_OUTCOME,
)
from formal.python.tools.toe_native_a_stress_energy_route_under_selected_u1_policy_result_review_report import (
    A_STRESS_ENERGY_ROUTE_RESULT,
    A_STRESS_ENERGY_ROUTE_REVIEW_RESULT,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CONVENTION_SCOPE,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    F_DEFINITION_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_SELECTOR_CANDIDATE,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTOR_ROUTE_OPTIONS,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_stress_energy_route_under_selected_u1_policy_result_review_report.py"
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


def test_a_stress_energy_route_result_review_files_exist() -> None:
    for path in [
        A_STRESS_ENERGY_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_stress_energy_route_result_review_accepts_route_only() -> None:
    packet = _json(A_STRESS_ENERGY_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == A_STRESS_ENERGY_PACKET_OUTCOME
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == A_STRESS_ENERGY_ROUTE_REVIEW_RESULT
    assert review["a_stress_energy_route_result"] == A_STRESS_ENERGY_ROUTE_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review()
        == review
    )


def test_a_stress_energy_route_result_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 14
    assert review["review_criteria_accepted_count"] == 14
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "selected_u1_policy_preserved",
        "A_smooth_real_one_form_preserved",
        "F_dA_preserved",
        "vacuum_route_preserved",
        "stress_energy_formula_preserved",
        "convention_sensitivity_preserved",
        "J_nu_not_derived",
        "current_conservation_not_proved",
        "source_admissibility_not_proved",
        "a_relevant_ck_rules_not_constructed",
        "sourced_maxwell_closure_not_claimed",
        "em_qft_gr_closure_not_claimed",
        "master_action_not_promoted",
        "next_selector_authorized",
    }
    assert review["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert review["F_definition_policy"] == F_DEFINITION_POLICY
    assert review["metric_signature_policy"] == METRIC_SIGNATURE_POLICY
    assert review["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert review["source_route_still_blocked"] == SOURCE_ROUTE_STILL_BLOCKED
    assert (
        review["stress_energy_under_selected_u1_policy"]
        == STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
    )
    assert review["convention_scope"] == CONVENTION_SCOPE
    assert review["stress_energy_route_accepted"] is True
    assert review["gauge_stress_energy_route_accepted"] is True
    assert review["stress_energy_formula_preserved"] is True
    assert review["convention_scope_retained"] is True


def test_a_stress_energy_route_result_review_selects_selector_not_route() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selector_authorized"] is True
    assert review["recommended_selector_candidate"] == RECOMMENDED_SELECTOR_CANDIDATE
    assert review["selector_route_options"] == SELECTOR_ROUTE_OPTIONS
    assert review["selector_route_option_count"] == 4
    assert review["recommended_selector_candidate_recorded"] is True
    assert review["source_admissibility_review_recommended_for_selector"] is True
    assert review["source_admissibility_review_selected_here"] is False
    assert review["current_coupling_route_selected_here"] is False
    assert review["current_conservation_route_selected_here"] is False
    assert review["A_relevant_C_k_route_selected_here"] is False


def test_a_stress_energy_route_result_review_retains_expected_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "stress_energy_source_admissibility_proved",
        "stress_energy_as_gravity_source_authorized",
        "current_route_derived",
        "current_source_route_constructed",
        "matter_current_J_nu_derived",
        "J_nu_derived",
        "psi_current_route_constructed",
        "psi_derived_current",
        "external_current_policy_selected",
        "external_current_native_derivation_selected",
        "current_conservation_proved",
        "A_source_admissibility_proved",
        "A_relevant_C_k_rules_constructed",
        "sourced_maxwell_equation_derived",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "canonical_master_action_promoted",
        "master_action_promoted",
        "empirical_validation_claimed",
    ]:
        assert review[key] is False, key
    for phrase in [
        "accepts the convention-sensitive U(1) gauge stress-energy route only",
        "does not derive J^nu",
        "does not derive a psi-current route",
        "does not select an external current as native derivation",
        "does not prove current conservation",
        "does not prove A-source admissibility",
        "does not construct A-relevant C_k rules",
        "does not claim sourced Maxwell closure",
        "does not close EM",
        "does not close QFT-GR",
        "does not authorize semiclassical coupling",
        "does not promote the master action",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_a_stress_energy_route_result_review_rotates_live_target_to_selector() -> None:
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
        "ToeNativeAStressEnergyRouteUnderSelectedU1PolicyResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_"
        "20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["stress_energy_route_accepted"] == "yes"
    assert consumed["gauge_stress_energy_route_accepted"] == "yes"
    assert consumed["stress_energy_formula_preserved"] == "yes"
    assert consumed["A_source_admissibility_proved"] == "no"
    assert consumed["A_relevant_C_k_rules_constructed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["selector_prepared"] == "no"
    assert active_row["selector_executed"] == "no"
    assert active_row["packet_result"] == "PENDING"
    assert active_row["recommended_selector_candidate"] == RECOMMENDED_SELECTOR_CANDIDATE
    assert active_row["route_option_count"] == "4"
    assert active_row["source_admissibility_review_selected"] == "no"
    assert active_row["current_coupling_route_selected"] == "no"
    assert active_row["current_conservation_route_selected"] == "no"
    assert active_row["A_relevant_C_k_route_selected"] == "no"
    assert active_row["current_route_derived"] == "no"
    assert active_row["A_source_admissibility_proved"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_stress_energy_route_result_review_lean_and_surface_mirrors() -> None:
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
        A_STRESS_ENERGY_ROUTE_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        RECOMMENDED_SELECTOR_CANDIDATE,
        "ToeNativeAStressEnergyRouteUnderSelectedU1PolicyResultReview",
        "HISTORICAL_TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_stress_energy_route_under_selected_u1_policy_result",
        "HISTORICAL_TOE_NATIVE_A_ROUTE_SELECTION_AFTER_STRESS_ENERGY_ROUTE_CURRENT_LIVE_NEXT_TARGET_v0: "
        "select_next_toe_native_A_route_after_stress_energy_route",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_vacuum_source_admissibility_identity_packet",
        "T^A_{mu nu} = - F_{mu alpha} F_{nu}{}^{alpha} + "
        "1/4 g_{mu nu} F_{alpha beta} F^{alpha beta}",
        "convention-sensitive",
        "does not derive J^nu",
        "does not prove A-source admissibility",
        "does not construct A-relevant C_k rules",
        "does not close QFT-GR",
        "master-action promotion remain blocked",
    ]:
        assert token in joined


def test_a_stress_energy_route_result_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_stress_energy_route_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_stress_energy_route_under_selected_u1_policy_result_review_gate.py"
    )
