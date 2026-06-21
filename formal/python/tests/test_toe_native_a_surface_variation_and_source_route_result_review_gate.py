from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_surface_variation_and_source_route_packet_report import (
    A_SURFACE_ROUTE_PACKET_RESULT,
    DEFAULT_OUT as A_ROUTE_PACKET_PATH,
    OUTCOME_ID as A_ROUTE_PACKET_OUTCOME,
    RAW_GAUGE_ROUTE,
    RAW_VARIATION_ROUTE,
    SOURCE_FORM_ROUTE_SHAPE,
)
from formal.python.tools.toe_native_a_surface_variation_and_source_route_result_review_report import (
    A_SURFACE_ROUTE_REVIEW_RESULT,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONABELIAN_ROUTE_SHAPE,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POLICY_PACKET_ITEMS,
    PREFERRED_POLICY_PACKET_OUTCOME_CANDIDATES,
    SCHEMA_ID,
    VACUUM_ROUTE_SHAPE,
    build_toe_native_a_surface_variation_and_source_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_surface_variation_and_source_route_result_review_report.py"
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
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
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


def test_a_surface_route_result_review_files_exist() -> None:
    for path in [
        A_ROUTE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_surface_route_result_review_accepts_raw_route_only() -> None:
    packet = _json(A_ROUTE_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == A_ROUTE_PACKET_OUTCOME
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == A_SURFACE_ROUTE_REVIEW_RESULT
    assert review["a_surface_route_packet_result"] == A_SURFACE_ROUTE_PACKET_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["raw_gauge_route"] == RAW_GAUGE_ROUTE
    assert review["raw_variation_route"] == RAW_VARIATION_ROUTE
    assert review["source_form_route_shape"] == SOURCE_FORM_ROUTE_SHAPE
    assert review["raw_A_to_F_route_preserved"] is True
    assert review["raw_variation_route_preserved"] is True
    assert review["source_form_recorded_as_shape_only"] is True
    assert review["native_derivation_blocked"] is True
    assert build_toe_native_a_surface_variation_and_source_route_result_review() == review


def test_a_surface_route_result_review_records_gauge_policy_cautions() -> None:
    review = _json(DEFAULT_OUT)
    assert review["vacuum_route_shape_from_pure_gauge_term"] == VACUUM_ROUTE_SHAPE
    assert (
        review["nonabelian_route_shape_requires_gauge_covariant_derivative"]
        == NONABELIAN_ROUTE_SHAPE
    )
    assert review["source_route_requires_current_policy_or_matter_coupling"] is True
    assert review["gauge_policy_is_next_real_blocker"] is True
    assert review["policy_packet_items"] == POLICY_PACKET_ITEMS
    assert review["policy_packet_item_count"] == 9
    assert (
        review["preferred_policy_packet_outcome_candidates"]
        == PREFERRED_POLICY_PACKET_OUTCOME_CANDIDATES
    )
    assert review["preferred_policy_packet_outcome_candidate_count"] == 2
    assert review["downstream_progression"][1]["decision"] == NEXT_TARGET


def test_a_surface_route_result_review_retains_expected_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 13
    assert review["review_criteria_accepted_count"] == 13
    assert review["retained_blocker_count"] == 15
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "raw_A_to_F_route_preserved",
        "raw_variation_route_preserved",
        "source_form_recorded_as_shape_only",
        "gauge_group_not_selected",
        "bundle_domain_policy_not_selected",
        "current_not_derived",
        "stress_energy_not_derived",
        "current_conservation_not_proved",
        "source_admissibility_not_proved",
        "a_relevant_ck_rules_not_constructed",
        "em_closure_not_claimed",
        "qft_gr_closure_not_claimed",
        "master_action_not_promoted",
    }
    for key in [
        "formal_theorem_backed_gauge_derivation",
        "a_surface_variation_executed",
        "a_surface_variation_route_executed",
        "gauge_group_selected",
        "bundle_domain_for_A_selected",
        "definition_of_F_selected",
        "covariant_derivative_D_mu_convention_selected",
        "matter_current_J_nu_derived",
        "external_current_policy_selected",
        "gauge_fixing_selected",
        "boundary_terms_controlled",
        "stress_energy_T_A_derived",
        "source_admissibility_proved",
        "current_conservation_proved",
        "gauge_current_constraint_proved",
        "C_k_analogues_constructed",
        "source_bridge_transport_ck_analogues_constructed",
        "maxwell_equations_derived",
        "yang_mills_equations_derived",
        "field_equations_derived",
        "gauge_field_derived",
        "current_source_route_constructed",
        "stress_energy_route_constructed",
        "toe_native_gauge_derivation_claimed",
        "toe_native_A_source_route_constructed",
        "toe_native_A_source_admissibility_claimed",
        "toe_native_A_current_conservation_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_map_closed",
        "qft_gr_solved",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "em_closure_claimed",
        "em_qft_closure_claimed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "canonical_master_action_promoted",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    assert "raw A-surface gauge-route recording only" in review["non_claim_boundary"]
    assert "does not derive J^nu" in review["non_claim_boundary"]
    assert "does not construct A-relevant C_k rules" in review["non_claim_boundary"]


def test_a_surface_route_result_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_surface_route_result_review_rotates_live_target_to_gauge_policy_packet() -> None:
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
        "ToeNativeASurfaceVariationAndSourceRouteResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_RESULT_REVIEW_20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["gauge_policy_packet_authorized"] == "yes"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["raw_A_to_F_route_preserved"] == "yes"
    assert active_row["raw_variation_route_preserved"] == "yes"
    assert active_row["source_form_recorded_as_shape_only"] == "yes"
    assert active_row["gauge_policy_packet_authorized"] == "yes"
    assert active_row["policy_packet_prepared"] == "no"
    assert active_row["gauge_group_selected"] == "no"
    assert active_row["matter_current_J_nu_derived"] == "no"
    assert active_row["source_admissibility_proved"] == "no"
    assert active_row["current_conservation_proved"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_surface_route_result_review_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            CURRENT_AUTHORITY_AGGREGATE_PATH,
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
        A_SURFACE_ROUTE_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeASurfaceVariationAndSourceRouteResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_A_gauge_group_domain_and_current_policy_packet",
        "raw A-surface gauge-route",
        "nabla_mu F^{mu nu} = 0",
        "D_mu F^{mu nu} = J^nu",
        "external-current policy",
        "matter-coupling route",
        "no Maxwell/Yang-Mills derivation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
    ]:
        assert token in joined


def test_a_surface_route_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_surface_variation_and_source_route_result_review_gate.py"
    )
