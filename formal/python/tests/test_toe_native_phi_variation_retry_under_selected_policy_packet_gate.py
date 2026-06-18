from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_phi_signature_domain_and_potential_policy_packet_report import (
    DEFAULT_OUT as PHI_POLICY_PACKET_PATH,
    PHI_POLICY_PACKET_RESULT,
)
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIELD_DOMAIN_POLICY,
    FIELD_EULER_LAGRANGE_EQUATION,
    FIELD_VARIATION_FORM,
    KINETIC_CONVENTION_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    METRIC_VARIATION_CONVENTION,
    METRIC_VARIATION_FORM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_VARIATION_RETRY_RESULT,
    POTENTIAL_POLICY,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCALAR_FIELD_TYPE_POLICY,
    SCALAR_WITNESS_COMPARISON_DECISION,
    SCHEMA_ID,
    SELECTED_PHI_ACTION,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    VARIATION_POLICY,
    WRITTEN_SANDBOX_DIFFERENCE,
    build_toe_native_phi_variation_retry_under_selected_policy_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_variation_retry_under_selected_policy_packet_report.py"
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


def test_phi_variation_retry_packet_files_exist() -> None:
    for path in [
        PHI_POLICY_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_variation_retry_packet_records_route_without_native_claim() -> None:
    policy = _json(PHI_POLICY_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert policy["outcome_id"] == PHI_POLICY_PACKET_RESULT
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["phi_variation_retry_result"] == PHI_VARIATION_RETRY_RESULT
    assert packet["phi_policy_packet_result"] == PHI_POLICY_PACKET_RESULT
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_phi_variation_retry_under_selected_policy_packet() == packet


def test_phi_variation_retry_packet_calculation_fields() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["metric_signature_policy"] == METRIC_SIGNATURE_POLICY
    assert packet["scalar_field_type_policy"] == SCALAR_FIELD_TYPE_POLICY
    assert packet["field_domain_policy"] == FIELD_DOMAIN_POLICY
    assert packet["kinetic_convention_policy"] == KINETIC_CONVENTION_POLICY
    assert packet["box_operator_convention"] == BOX_OPERATOR_CONVENTION
    assert packet["potential_policy"] == POTENTIAL_POLICY
    assert packet["variation_policy"] == VARIATION_POLICY
    assert packet["ck_role_policy"] == CK_ROLE_POLICY
    assert packet["selected_phi_action"] == SELECTED_PHI_ACTION
    assert packet["field_variation_form"] == FIELD_VARIATION_FORM
    assert packet["field_variation_form"].startswith("delta_phi")
    assert packet["field_euler_lagrange_equation"] == FIELD_EULER_LAGRANGE_EQUATION
    assert packet["field_euler_lagrange_equation"] == (
        "Box_g phi_i + partial_i V(phi) = 0"
    )
    assert packet["metric_variation_convention"] == METRIC_VARIATION_CONVENTION
    assert "T^policy_{mu nu} = 2/sqrt(-g)" in packet["metric_variation_convention"]
    assert packet["metric_variation_form"] == METRIC_VARIATION_FORM
    assert packet["stress_energy_under_selected_policy"] == STRESS_ENERGY_UNDER_SELECTED_POLICY
    assert packet["scalar_witness_comparison_decision"] == (
        SCALAR_WITNESS_COMPARISON_DECISION
    )
    assert packet["written_sandbox_difference"] == WRITTEN_SANDBOX_DIFFERENCE
    assert packet["calculation_step_count"] == 8


def test_phi_variation_retry_packet_retains_expected_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["review_criteria_count"] == 10
    assert packet["review_criteria_accepted_count"] == 10
    assert packet["field_variation_computed"] is True
    assert packet["metric_variation_computed"] is True
    assert packet["stress_energy_route_recorded"] is True
    assert packet["scalar_witness_route_reproduced_under_selected_policy"] is True
    assert packet["sign_convention_verified_explicitly"] is True
    assert packet["literal_imported_sandbox_formula_copied"] is False
    assert packet["ck_allowed_to_modify_phi_equation"] is False
    assert packet["ck_variational_content_defined"] is False
    assert packet["ck_variational_content_still_blocked"] is True
    assert packet["native_generation_blocked"] is True
    assert packet["phi_variation_retry_executed"] is True
    assert packet["phi_variation_route_executed"] is True
    assert packet["phi_variation_derived_as_toe_native"] is False
    assert packet["phi_stress_energy_derived_as_toe_native"] is False
    for key in [
        "formal_theorem_backed_matter_derivation",
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
        assert packet[key] is False, key
    assert "convention-normalized symbolic calculation only" in packet["non_claim_boundary"]


def test_phi_variation_retry_packet_validation_policy_records_timeout_boundary() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == AGGREGATE_TIMEOUT_STATUS
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_variation_retry_packet_rotates_live_target_to_result_review() -> None:
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
        "ToeNativePhiVariationRetryUnderSelectedPolicyPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["phi_variation_retry_result"] == PHI_VARIATION_RETRY_RESULT
    assert consumed["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["phi_variation_retry_result"] == PHI_VARIATION_RETRY_RESULT
    assert active_row["field_euler_lagrange_equation"] == FIELD_EULER_LAGRANGE_EQUATION
    assert active_row["stress_energy_under_selected_policy"] == (
        STRESS_ENERGY_UNDER_SELECTED_POLICY
    )
    assert active_row["field_variation_computed"] == "yes"
    assert active_row["metric_variation_computed"] == "yes"
    assert active_row["stress_energy_route_recorded"] == "yes"
    assert active_row["scalar_witness_route_reproduced_under_selected_policy"] == "yes"
    assert active_row["literal_imported_sandbox_formula_copied"] == "no"
    assert active_row["ck_allowed_to_modify_phi_equation"] == "no"
    assert active_row["ck_variational_content_still_blocked"] == "yes"
    assert active_row["native_generation_blocked"] == "yes"
    assert active_row["symbolic_calculation_recorded"] == "yes"
    assert active_row["calculation_step_count"] == "8"
    assert active_row["review_criteria_count"] == "10"
    assert active_row["review_criteria_accepted_count"] == "10"
    assert active_row["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["source_conservation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["semiclassical_coupling_authorized"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_variation_retry_packet_lean_and_surface_mirrors() -> None:
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
        PHI_VARIATION_RETRY_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativePhiVariationRetryUnderSelectedPolicyPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_toe_native_phi_variation_retry_under_selected_policy_result",
        "PHI_VARIATION_ROUTE_REPRODUCES_SCALAR_WITNESS_UNDER_SELECTED_POLICY_NO_NATIVE_GENERATION_CLAIM",
        "Box_g phi_i + partial_i V(phi) = 0",
        "T^policy_{mu nu}",
        "convention normalization",
        "C_k remains inactive and undefined",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no semiclassical coupling",
        "no canonical master-action promotion",
    ]:
        assert token in joined


def test_phi_variation_retry_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_variation_retry_under_selected_policy_packet_gate.py"
    )
