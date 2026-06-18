from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_phi_surface_alignment_witness_closeout_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALIGNMENT_WITNESS_CLOSEOUT_STATUS,
    ALIGNMENT_WITNESS_STATUS,
    ARTIFACT_ID,
    CK_VARIATIONAL_CONTENT_FRONTIER_QUESTION,
    CLOSEOUT_RESULT,
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
    PHI_VARIATION_RETRY_RESULT,
    PHI_VARIATION_RETRY_REVIEW_OUTCOME,
    PHI_VARIATION_RETRY_REVIEW_RESULT,
    PHI_VARIATION_RETRY_RESULT_REVIEW_PATH,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCALAR_WITNESS_COMPARISON_DECISION,
    SCHEMA_ID,
    build_toe_native_phi_surface_alignment_witness_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_surface_alignment_witness_closeout_report.py"
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


def test_phi_surface_alignment_witness_closeout_files_exist() -> None:
    for path in [
        PHI_VARIATION_RETRY_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_surface_alignment_witness_closeout_accepts_expected_result() -> None:
    review = _json(PHI_VARIATION_RETRY_RESULT_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == PHI_VARIATION_RETRY_REVIEW_OUTCOME
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
    assert closeout["alignment_witness_status"] == ALIGNMENT_WITNESS_STATUS
    assert closeout["alignment_witness_closeout_status"] == (
        ALIGNMENT_WITNESS_CLOSEOUT_STATUS
    )
    assert closeout["ck_variational_content_frontier_question"] == (
        CK_VARIATIONAL_CONTENT_FRONTIER_QUESTION
    )
    assert closeout["phi_variation_retry_review_result"] == (
        PHI_VARIATION_RETRY_REVIEW_RESULT
    )
    assert closeout["phi_variation_retry_result"] == PHI_VARIATION_RETRY_RESULT
    assert build_toe_native_phi_surface_alignment_witness_closeout() == closeout


def test_phi_surface_alignment_witness_closeout_records_required_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 8
    assert closeout["closeout_criteria_accepted_count"] == 8
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "selected_phi_policy_was_used",
        "phi_variation_route_matched_scalar_witness_after_normalization",
        "master_action_alignment_not_native_derivation",
        "potential_selected_not_derived",
        "ck_undefined_and_inactive",
        "no_source_admissibility_or_conservation_newly_claimed",
        "no_qft_gr_closure_claimed",
        "no_master_action_promotion_claimed",
    }
    assert closeout["selected_phi_policy_was_used"] is True
    assert closeout["phi_variation_route_matched_scalar_witness_after_normalization"] is True
    assert closeout["master_action_alignment_not_native_derivation"] is True
    assert closeout["potential_selected_not_derived"] is True
    assert closeout["ck_undefined_and_inactive"] is True
    assert closeout["no_source_admissibility_or_conservation_newly_claimed"] is True
    assert closeout["no_qft_gr_closure_claimed"] is True
    assert closeout["no_master_action_promotion_claimed"] is True
    assert closeout["scalar_witness_comparison_decision"] == (
        SCALAR_WITNESS_COMPARISON_DECISION
    )
    assert closeout["scalar_witness_match_only_after_convention_normalization"] is True
    assert closeout["literal_imported_sandbox_formula_copied"] is False


def test_phi_surface_alignment_witness_closeout_retains_expected_nonclaims() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["alignment_witness_closed"] is True
    assert closeout["alignment_witness_closeout_prepared"] is True
    assert closeout["ck_variational_content_packet_authorized"] is True
    assert closeout["ck_variational_content_defined"] is False
    assert closeout["ck_allowed_to_modify_phi_equation"] is False
    assert closeout["potential_derived"] is False
    assert closeout["native_generation_theorem_claimed"] is False
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
        assert closeout[key] is False, key
    assert "alignment witness only" in closeout["non_claim_boundary"]
    assert "does not supply a native-generation theorem" in closeout["non_claim_boundary"]
    assert "does not define or vary C_k content" in closeout["non_claim_boundary"]


def test_phi_surface_alignment_witness_closeout_validation_policy_records_timeout() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_surface_alignment_witness_closeout_rotates_live_target_to_ck_packet() -> None:
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
        "ToeNativePhiSurfaceAlignmentWitnessCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["alignment_witness_closeout_prepared"] == "yes"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["alignment_witness_closeout_prepared"] == "yes"
    assert active_row["alignment_witness_closed"] == "yes"
    assert active_row["ck_variational_content_packet_authorized"] == "yes"
    assert active_row["ck_variational_content_packet_prepared"] == "no"
    assert active_row["ck_variational_content_defined"] == "no"
    assert active_row["native_generation_theorem_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["source_conservation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_surface_alignment_witness_closeout_lean_and_surface_mirrors() -> None:
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
        "ToeNativePhiSurfaceAlignmentWitnessCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_phi_ck_variational_content_packet",
        "MASTER_ACTION_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSED_NO_NATIVE_GENERATION_OR_CK_CONTENT",
        "master-action alignment witness",
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


def test_phi_surface_alignment_witness_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_surface_alignment_witness_closeout_gate.py"
    )
