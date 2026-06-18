from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_phi_ck_variational_content_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    BLOCKER_ID,
    CK_INDEPENDENCE_CASE,
    CK_VARIATION_FORMAL_SLOT,
    CK_VARIATION_TARGET,
    CK_VARIATIONAL_CONTENT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    LEFT_HAND_FORCE_CONVENTION,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MASTER_ACTION_CK_SURFACE,
    MASTER_ACTION_DOC_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NORMALIZED_PHI_CK_EQUATION,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_ALIGNMENT_CLOSEOUT_OUTCOME,
    PHI_ALIGNMENT_CLOSEOUT_PATH,
    QFTGR_AGGREGATE_PATH,
    RAW_PHI_ROUTE_PACKET_PATH,
    RAW_TOTAL_PHI_CK_EQUATION,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCE_FROM_CK_UNDER_SELECTED_POLICY,
    build_toe_native_phi_ck_variational_content_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_ck_variational_content_packet_report.py"
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


def test_phi_ck_variational_content_packet_files_exist() -> None:
    for path in [
        PHI_ALIGNMENT_CLOSEOUT_PATH,
        RAW_PHI_ROUTE_PACKET_PATH,
        MASTER_ACTION_DOC_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_ck_variational_content_packet_accepts_blocked_result() -> None:
    closeout = _json(PHI_ALIGNMENT_CLOSEOUT_PATH)
    packet = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == PHI_ALIGNMENT_CLOSEOUT_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == CK_VARIATIONAL_CONTENT_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["phi_alignment_closeout_outcome"] == PHI_ALIGNMENT_CLOSEOUT_OUTCOME
    assert build_toe_native_phi_ck_variational_content_packet() == packet


def test_phi_ck_variational_content_packet_records_symbolic_variation_slot() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["master_action_ck_surface"] == MASTER_ACTION_CK_SURFACE
    assert packet["ck_variation_target"] == CK_VARIATION_TARGET
    assert packet["ck_variation_formal_slot"] == CK_VARIATION_FORMAL_SLOT
    assert packet["raw_total_phi_ck_equation"] == RAW_TOTAL_PHI_CK_EQUATION
    assert packet["normalized_phi_ck_equation"] == NORMALIZED_PHI_CK_EQUATION
    assert packet["source_from_ck_under_selected_policy"] == (
        SOURCE_FROM_CK_UNDER_SELECTED_POLICY
    )
    assert packet["left_hand_force_convention"] == LEFT_HAND_FORCE_CONVENTION
    assert packet["ck_independence_case"] == CK_INDEPENDENCE_CASE
    assert packet["blocker_id"] == BLOCKER_ID
    assert packet["generic_ck_surface_present"] is True
    assert packet["concrete_ck_functionals_found"] == []
    assert packet["concrete_ck_functional_definition_available"] is False
    assert packet["ck_variational_derivative_defined"] is False
    assert packet["ck_variational_content_recorded_symbolically"] is True
    assert packet["ck_variational_content_constructed"] is False
    assert packet["ck_variational_content_blocked"] is True
    assert packet[
        "ck_variational_content_blocked_by_unspecified_constraint_functionals"
    ] is True


def test_phi_ck_variational_content_packet_tests_all_requested_roles() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["ck_effect_test_count"] == 7
    matrix = {row["row_id"]: row for row in packet["ck_effect_test_matrix"]}
    assert set(matrix) == {
        "generate_phi_equation",
        "modify_phi_equation",
        "restrict_allowed_potential",
        "enforce_source_conservation",
        "connect_phi_to_another_pillar",
        "produce_new_residual_law",
        "produce_possible_falsifier",
    }
    assert matrix["modify_phi_equation"]["symbolic_status"] == (
        "formal_slot_recorded_only"
    )
    for row in matrix.values():
        assert row["can_be_tested_now"] is False
    assert packet["ck_phi_equation_generation_constructed"] is False
    assert packet["ck_phi_equation_modification_route_recorded_symbolically"] is True
    assert packet["ck_phi_equation_modification_constructed"] is False
    assert packet["ck_potential_restriction_constructed"] is False
    assert packet["ck_source_conservation_enforced"] is False
    assert packet["ck_cross_pillar_connection_constructed"] is False
    assert packet["ck_new_residual_law_constructed"] is False
    assert packet["ck_possible_falsifier_produced"] is False
    assert packet["ck_phi_independence_case_recorded"] is True
    assert packet["ck_phi_independence_selected"] is False
    assert packet["ck_constraint_family_selected"] is False
    assert packet["ck_constraint_functional_definition_required"] is True
    assert packet["master_action_ck_definition_packet_authorized"] is True


def test_phi_ck_variational_content_packet_retains_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "formal_theorem_backed_matter_derivation",
        "native_generation_theorem_claimed",
        "derived_v_phi_claimed",
        "potential_derived",
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
        assert packet[key] is False, key
    assert "blocks real C_k variational content" in packet["non_claim_boundary"]
    assert "does not supply a native-generation theorem" in packet["non_claim_boundary"]
    assert "does not construct C_k modification or conservation" in (
        packet["non_claim_boundary"]
    )


def test_phi_ck_variational_content_packet_validation_policy_records_timeout() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_ck_variational_content_packet_rotates_live_target_to_ck_definition() -> None:
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
        "ToeNativePhiCKVariationalContentPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == CK_VARIATIONAL_CONTENT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["ck_variational_content_packet_prepared"] == "yes"
    assert consumed["ck_variational_content_blocked"] == "yes"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == CK_VARIATIONAL_CONTENT_RESULT
    assert active_row["ck_constraint_functional_definition_packet_prepared"] == "no"
    assert active_row["master_action_ck_definition_packet_authorized"] == "yes"
    assert active_row["ck_variational_content_recorded_symbolically"] == "yes"
    assert active_row["ck_variational_content_constructed"] == "no"
    assert active_row["ck_variational_content_blocked"] == "yes"
    assert active_row["ck_phi_equation_generation_constructed"] == "no"
    assert active_row["ck_potential_restriction_constructed"] == "no"
    assert active_row["ck_source_conservation_enforced"] == "no"
    assert active_row["ck_cross_pillar_connection_constructed"] == "no"
    assert active_row["ck_new_residual_law_constructed"] == "no"
    assert active_row["ck_possible_falsifier_produced"] == "no"
    assert active_row["native_generation_theorem_claimed"] == "no"
    assert active_row["source_conservation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_ck_variational_content_packet_lean_and_surface_mirrors() -> None:
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
        CK_VARIATIONAL_CONTENT_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativePhiCKVariationalContentPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_master_action_ck_constraint_functional_definition_packet",
        "CK-FUNCTIONAL-DEFINITION-MISSING-FOR-PHI-VARIATION",
        "Box_g phi_i + partial_i V(phi) = sum_k lambda_k delta C_k/delta phi_i",
        "C_k does not yet generate phi",
        "V(phi) remains smooth bounded-below but not derived",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
    ]:
        assert token in joined


def test_phi_ck_variational_content_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_ck_variational_content_packet_gate.py"
    )
