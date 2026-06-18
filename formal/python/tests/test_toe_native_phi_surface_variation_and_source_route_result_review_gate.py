from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_phi_surface_variation_and_source_route_packet_report import (
    DEFAULT_OUT as PHI_ROUTE_PACKET_PATH,
    OUTCOME_ID as PHI_ROUTE_PACKET_OUTCOME,
    PHI_ROUTE_PACKET_RESULT,
)
from formal.python.tools.toe_native_phi_surface_variation_and_source_route_result_review_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFERRED_CK_TARGET,
    FIELD_CONTRACT_ITEMS,
    IMPORTED_SCALAR_COMPARISON_DECISION,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_ROUTE_REVIEW_RESULT,
    SCHEMA_ID,
    SOURCE_ROUTE_STATUS_DECISION,
    TOE_NATIVE_STATUS_DECISION,
    build_toe_native_phi_surface_variation_and_source_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_surface_variation_and_source_route_result_review_report.py"
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


def test_phi_route_result_review_files_exist() -> None:
    for path in [
        PHI_ROUTE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_route_result_review_accepts_raw_route_and_blocks_native_derivation() -> None:
    packet = _json(PHI_ROUTE_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == PHI_ROUTE_PACKET_OUTCOME
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == PHI_ROUTE_REVIEW_RESULT
    assert review["phi_route_packet_result"] == PHI_ROUTE_PACKET_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["deferred_ck_variational_content_target"] == DEFERRED_CK_TARGET
    assert review["source_route_status_decision"] == SOURCE_ROUTE_STATUS_DECISION
    assert review["imported_scalar_comparison_decision"] == IMPORTED_SCALAR_COMPARISON_DECISION
    assert review["toe_native_status_decision"] == TOE_NATIVE_STATUS_DECISION
    assert review["raw_symbolic_phi_route_recorded"] is True
    assert review["native_derivation_blocked"] is True
    assert review["imported_scalar_witness_not_promoted"] is True
    assert review["ck_variational_content_still_undefined"] is True
    assert build_toe_native_phi_surface_variation_and_source_route_result_review() == review


def test_phi_route_result_review_selects_signature_domain_potential_before_ck() -> None:
    review = _json(DEFAULT_OUT)
    assert review["field_contract_items"] == FIELD_CONTRACT_ITEMS
    assert review["field_contract_item_count"] == 7
    assert review["metric_signature_policy_required"] is True
    assert review["scalar_field_domain_policy_required"] is True
    assert review["number_of_phi_fields_policy_required"] is True
    assert review["kinetic_sign_policy_required"] is True
    assert review["potential_policy_required"] is True
    assert review["variation_convention_policy_required"] is True
    assert review["boundary_assumption_policy_required"] is True
    assert review["signature_domain_potential_policy_packet_authorized"] is True
    assert review["ck_variational_content_packet_deferred"] is True
    assert review["downstream_progression"][1]["decision"] == NEXT_TARGET
    assert review["downstream_progression"][2]["decision"] == DEFERRED_CK_TARGET


def test_phi_route_result_review_retains_expected_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 10
    assert review["review_criteria_accepted_count"] == 10
    assert review["retained_blocker_count"] == 6
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "raw_symbolic_phi_route_recorded",
        "native_derivation_blocked",
        "imported_scalar_witness_not_promoted",
        "ck_variational_content_still_undefined",
        "source_admissibility_not_claimed",
        "conservation_not_claimed",
        "qft_gr_closure_not_claimed",
        "master_action_not_promoted",
        "retained_blockers_are_the_right_frontier",
        "next_target_sets_scalar_contract_before_ck",
    }
    for key in [
        "formal_theorem_backed_matter_derivation",
        "phi_variation_route_executed",
        "phi_variation_derived_as_toe_native",
        "phi_stress_energy_derived_as_toe_native",
        "toe_native_phi_source_route_constructed",
        "toe_native_phi_source_admissibility_claimed",
        "toe_native_phi_source_conservation_claimed",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
        "toe_matter_sector_derived",
        "toe_matter_model_derived",
        "standard_model_derivation_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "source_map_closed",
        "qft_gr_solved",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
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
    assert "raw symbolic phi-route recording only" in review["non_claim_boundary"]


def test_phi_route_result_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_route_result_review_rotates_live_target_to_policy_packet() -> None:
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
        "ToeNativePhiSurfaceVariationAndSourceRouteResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_RESULT_REVIEW_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["raw_symbolic_phi_route_recorded"] == "yes"
    assert active_row["native_derivation_blocked"] == "yes"
    assert active_row["imported_scalar_witness_not_promoted"] == "yes"
    assert active_row["ck_variational_content_still_undefined"] == "yes"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["source_conservation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_route_result_review_lean_and_surface_mirrors() -> None:
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
        PHI_ROUTE_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DEFERRED_CK_TARGET,
        "ToeNativePhiSurfaceVariationAndSourceRouteResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_phi_signature_domain_and_potential_policy_packet",
        "raw symbolic phi-route",
        "native derivation",
        "C_k variational content",
        "imported scalar witness",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no semiclassical coupling",
        "no canonical master-action promotion",
    ]:
        assert token in joined


def test_phi_route_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_surface_variation_and_source_route_result_review_gate.py"
    )
