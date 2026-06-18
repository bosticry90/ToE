from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_phi_signature_domain_and_potential_policy_packet_report import (
    ARTIFACT_ID,
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFERRED_CK_TARGET,
    FIELD_DOMAIN_POLICY,
    KINETIC_CONVENTION_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_POLICY_DECISION,
    PHI_POLICY_PACKET_RESULT,
    POLICY_ITEMS,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SCHEMA_ID,
    SELECTED_PHI_EQUATION_NO_CK,
    VARIATION_POLICY,
    build_toe_native_phi_signature_domain_and_potential_policy_packet,
)
from formal.python.tools.toe_native_phi_surface_variation_and_source_route_result_review_report import (
    DEFAULT_OUT as PHI_ROUTE_REVIEW_PATH,
    OUTCOME_ID as PHI_ROUTE_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_phi_signature_domain_and_potential_policy_packet_report.py"
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


def test_phi_policy_packet_files_exist() -> None:
    for path in [
        PHI_ROUTE_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_policy_packet_selects_partial_policy_and_blocks_ck() -> None:
    review = _json(PHI_ROUTE_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == PHI_ROUTE_REVIEW_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["phi_policy_decision"] == PHI_POLICY_DECISION
    assert packet["phi_policy_packet_result"] == PHI_POLICY_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["deferred_ck_variational_content_target"] == DEFERRED_CK_TARGET
    assert packet["policy_status"] == "partial_nonpromotional_selection"
    assert packet["signature_domain_potential_policy_selected"] is True
    assert packet["ck_allowed_to_modify_phi_equation"] is False
    assert packet["ck_variational_content_defined"] is False
    assert packet["ck_variational_content_still_blocked"] is True
    assert build_toe_native_phi_signature_domain_and_potential_policy_packet() == packet


def test_phi_policy_packet_records_selected_contract() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["policy_item_count"] == 8
    assert packet["policy_selected_count"] == 7
    assert packet["policy_blocked_count"] == 1
    assert [row["policy_id"] for row in packet["policy_items"]] == [
        "metric_signature",
        "scalar_field_type",
        "field_domain",
        "kinetic_convention",
        "box_operator",
        "potential_policy",
        "variation_policy",
        "ck_role",
    ]
    assert packet["metric_signature_policy"] == METRIC_SIGNATURE_POLICY
    assert packet["scalar_field_type_policy"] == SCALAR_FIELD_TYPE_POLICY
    assert packet["field_domain_policy"] == FIELD_DOMAIN_POLICY
    assert packet["kinetic_convention_policy"] == KINETIC_CONVENTION_POLICY
    assert packet["box_operator_convention"] == BOX_OPERATOR_CONVENTION
    assert packet["potential_policy"] == POTENTIAL_POLICY
    assert packet["variation_policy"] == VARIATION_POLICY
    assert packet["ck_role_policy"] == CK_ROLE_POLICY
    assert packet["selected_phi_equation_no_ck"] == SELECTED_PHI_EQUATION_NO_CK
    assert POLICY_ITEMS == [
        "metric signature",
        "scalar field type",
        "field domain",
        "kinetic convention",
        "box operator",
        "potential policy",
        "variation policy",
        "C_k role",
    ]


def test_phi_policy_packet_retains_expected_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["review_criteria_count"] == 10
    assert packet["review_criteria_accepted_count"] == 10
    assert {row["row_id"] for row in packet["review_criteria"]} == {
        "consumes_expected_policy_packet_target",
        "metric_signature_selected",
        "scalar_field_type_selected",
        "field_domain_selected",
        "kinetic_and_box_conventions_selected",
        "potential_policy_partially_selected",
        "variation_policy_selected",
        "ck_variational_content_blocked",
        "imported_scalar_witness_not_promoted",
        "next_retry_authorized_under_selected_policy",
    }
    assert packet["phi_variation_retry_authorized"] is True
    assert packet["phi_variation_retry_executed"] is False
    assert packet["imported_scalar_witness_not_promoted"] is True
    assert packet["native_derivation_blocked"] is True
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
        assert packet[key] is False, key
    assert "selects calculation conventions only" in packet["non_claim_boundary"]


def test_phi_policy_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_policy_packet_rotates_live_target_to_variation_retry() -> None:
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
        "ToeNativePhiSignatureDomainAndPotentialPolicyPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["phi_policy_packet_result"] == PHI_POLICY_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["phi_policy_decision"] == PHI_POLICY_DECISION
    assert active_row["metric_signature_policy"] == METRIC_SIGNATURE_POLICY
    assert active_row["ck_allowed_to_modify_phi_equation"] == "no"
    assert active_row["ck_variational_content_still_blocked"] == "yes"
    assert active_row["phi_variation_retry_authorized"] == "yes"
    assert active_row["phi_variation_retry_executed"] == "no"
    assert active_row["toe_native_matter_derivation_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_policy_packet_lean_and_surface_mirrors() -> None:
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
        PHI_POLICY_DECISION,
        PHI_POLICY_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DEFERRED_CK_TARGET,
        "ToeNativePhiSignatureDomainAndPotentialPolicyPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_phi_variation_retry_under_selected_policy",
        "PHI_POLICY_PARTIALLY_SELECTED_CK_VARIATIONAL_CONTENT_STILL_BLOCKED",
        "(+,-,-,-)",
        "finite real scalar multiplet",
        "smooth finite-action",
        "C_k variational content",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no semiclassical coupling",
        "no canonical master-action promotion",
    ]:
        assert token in joined


def test_phi_policy_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_phi_signature_domain_and_potential_policy_packet_gate.py"
    )
