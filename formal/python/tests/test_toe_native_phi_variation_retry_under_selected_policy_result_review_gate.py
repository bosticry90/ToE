from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_packet_report import (
    DEFAULT_OUT as PHI_VARIATION_RETRY_PACKET_PATH,
    OUTCOME_ID as PHI_VARIATION_RETRY_PACKET_OUTCOME,
    PHI_VARIATION_RETRY_RESULT,
)
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALIGNMENT_WITNESS_STATUS,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DEFERRED_CK_TARGET,
    FIELD_EULER_LAGRANGE_EQUATION,
    FIELD_VARIATION_FORM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_VARIATION_CONVENTION,
    METRIC_VARIATION_FORM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_VARIATION_RETRY_REVIEW_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCALAR_WITNESS_COMPARISON_DECISION,
    SCHEMA_ID,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    build_toe_native_phi_variation_retry_under_selected_policy_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_variation_retry_under_selected_policy_result_review_report.py"
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


def test_phi_variation_retry_result_review_files_exist() -> None:
    for path in [
        PHI_VARIATION_RETRY_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_variation_retry_result_review_accepts_alignment_witness_only() -> None:
    retry = _json(PHI_VARIATION_RETRY_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert retry["outcome_id"] == PHI_VARIATION_RETRY_PACKET_OUTCOME
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == PHI_VARIATION_RETRY_REVIEW_RESULT
    assert review["phi_variation_retry_result"] == PHI_VARIATION_RETRY_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["deferred_ck_variational_content_target"] == DEFERRED_CK_TARGET
    assert review["alignment_witness_status"] == ALIGNMENT_WITNESS_STATUS
    assert build_toe_native_phi_variation_retry_under_selected_policy_result_review() == review


def test_phi_variation_retry_result_review_accepts_required_review_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 10
    assert review["review_criteria_accepted_count"] == 10
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "selected_phi_policy_carried_forward_exactly",
        "field_variation_recorded_under_selected_policy",
        "metric_variation_source_route_recorded_under_selected_policy",
        "scalar_witness_match_only_after_convention_normalization",
        "ck_remains_undefined_and_inactive",
        "potential_smooth_bounded_below_not_derived",
        "native_generation_theorem_not_claimed",
        "source_conservation_closure_and_promotion_not_claimed",
        "alignment_witness_interpretation_accepted",
        "closeout_selected_before_ck_content_packet",
    }
    assert review["selected_phi_policy_carried_forward_exactly"] is True
    assert review["field_variation_recorded_under_selected_policy"] is True
    assert review["metric_variation_source_route_recorded_under_selected_policy"] is True
    assert review["scalar_witness_route_match_accepted"] is True
    assert review["scalar_witness_match_only_after_convention_normalization"] is True
    assert review["literal_imported_sandbox_formula_copied"] is False
    assert review["field_variation_form"] == FIELD_VARIATION_FORM
    assert review["field_euler_lagrange_equation"] == FIELD_EULER_LAGRANGE_EQUATION
    assert review["metric_variation_convention"] == METRIC_VARIATION_CONVENTION
    assert review["metric_variation_form"] == METRIC_VARIATION_FORM
    assert review["stress_energy_under_selected_policy"] == STRESS_ENERGY_UNDER_SELECTED_POLICY
    assert review["scalar_witness_comparison_decision"] == (
        SCALAR_WITNESS_COMPARISON_DECISION
    )


def test_phi_variation_retry_result_review_retains_expected_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["ck_remains_undefined_and_inactive"] is True
    assert review["ck_allowed_to_modify_phi_equation"] is False
    assert review["ck_variational_content_defined"] is False
    assert review["ck_variational_content_still_blocked"] is True
    assert review["potential_smooth_bounded_below"] is True
    assert review["potential_derived"] is False
    assert review["native_generation_theorem_claimed"] is False
    assert review["native_generation_blocked"] is True
    assert review["alignment_witness_closeout_authorized"] is True
    assert review["ck_variational_content_packet_deferred"] is True
    assert review["phi_variation_retry_executed"] is True
    assert review["phi_variation_route_executed"] is True
    for key in [
        "formal_theorem_backed_matter_derivation",
        "phi_variation_derived_as_toe_native",
        "phi_stress_energy_derived_as_toe_native",
        "toe_native_phi_source_route_constructed",
        "toe_native_phi_source_admissibility_claimed",
        "toe_native_phi_source_conservation_claimed",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "standard_model_derivation_claimed",
        "source_admissibility_claimed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "canonical_master_action_promoted",
        "master_action_promoted",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    assert "alignment witness only" in review["non_claim_boundary"]
    assert "does not supply a native-generation theorem" in review["non_claim_boundary"]


def test_phi_variation_retry_result_review_validation_policy_records_timeout_boundary() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == AGGREGATE_TIMEOUT_STATUS
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_variation_retry_result_review_rotates_live_target_to_closeout() -> None:
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
        "ToeNativePhiVariationRetryUnderSelectedPolicyResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_RESULT_REVIEW_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["alignment_witness_status"] == ALIGNMENT_WITNESS_STATUS

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["alignment_witness_status"] == ALIGNMENT_WITNESS_STATUS
    assert active_row["alignment_witness_closeout_authorized"] == "yes"
    assert active_row["alignment_witness_closeout_prepared"] == "no"
    assert active_row["ck_variational_content_packet_deferred"] == "yes"
    assert active_row["native_generation_theorem_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_variation_retry_result_review_lean_and_surface_mirrors() -> None:
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
        PHI_VARIATION_RETRY_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DEFERRED_CK_TARGET,
        "ToeNativePhiVariationRetryUnderSelectedPolicyResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_phi_surface_alignment_witness_closeout",
        "MASTER_ACTION_PHI_SURFACE_ALIGNMENT_WITNESS_ACCEPTED_NO_NATIVE_GENERATION",
        "master-action alignment witness only",
        "V(phi) remains smooth bounded-below but not derived",
        "C_k remains inactive and undefined",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
    ]:
        assert token in joined


def test_phi_variation_retry_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_variation_retry_under_selected_policy_result_review_gate.py"
    )
