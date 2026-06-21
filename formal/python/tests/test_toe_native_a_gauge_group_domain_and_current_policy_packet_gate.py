from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_gauge_group_domain_and_current_policy_packet_report import (
    A_FIELD_DOMAIN_POLICY,
    A_GAUGE_POLICY_DECISION,
    A_GAUGE_POLICY_PACKET_RESULT,
    ARTIFACT_ID,
    CK_ROLE_POLICY,
    CONSUMED_TARGET,
    CURRENT_POLICY,
    CURRENT_ROUTE_SHAPE,
    DEFAULT_OUT,
    DEFERRED_A_CK_RULE_TARGET,
    DEFERRED_CURRENT_POLICY_TARGET,
    DERIVATIVE_CONVENTION_POLICY,
    F_DEFINITION_POLICY,
    GAUGE_FIXING_POLICY,
    GAUGE_GROUP_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POLICY_ITEMS,
    PURE_GAUGE_EQUATION_ROUTE,
    SCHEMA_ID,
    VARIATION_POLICY,
    build_toe_native_a_gauge_group_domain_and_current_policy_packet,
)
from formal.python.tools.toe_native_a_surface_variation_and_source_route_result_review_report import (
    DEFAULT_OUT as A_ROUTE_REVIEW_PATH,
    OUTCOME_ID as A_ROUTE_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_gauge_group_domain_and_current_policy_packet_report.py"
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


def test_a_gauge_policy_packet_files_exist() -> None:
    for path in [
        A_ROUTE_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_gauge_policy_packet_selects_u1_and_blocks_current_derivation() -> None:
    review = _json(A_ROUTE_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == A_ROUTE_REVIEW_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["a_gauge_policy_decision"] == A_GAUGE_POLICY_DECISION
    assert packet["a_gauge_policy_packet_result"] == A_GAUGE_POLICY_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["deferred_current_policy_target"] == DEFERRED_CURRENT_POLICY_TARGET
    assert packet["deferred_A_ck_rule_target"] == DEFERRED_A_CK_RULE_TARGET
    assert packet["policy_status"] == (
        "minimal_abelian_policy_selected_current_derivation_blocked"
    )
    assert packet["u1_route_selected"] is True
    assert packet["minimal_abelian_route_selected"] is True
    assert packet["current_derivation_blocked"] is True
    assert packet["external_current_policy_selected"] is False
    assert packet["psi_derived_current_deferred"] is True
    assert build_toe_native_a_gauge_group_domain_and_current_policy_packet() == packet


def test_a_gauge_policy_packet_records_selected_contract() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["policy_item_count"] == 9
    assert packet["policy_selected_count"] == 7
    assert packet["policy_blocked_count"] == 2
    assert [row["policy_id"] for row in packet["policy_items"]] == [
        "gauge_group",
        "A_field_domain",
        "F_definition",
        "derivative_convention",
        "boundary_variation_policy",
        "pure_gauge_equation_route",
        "current_policy",
        "gauge_fixing_status",
        "A_relevant_C_k_role",
    ]
    assert packet["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert packet["selected_gauge_group"] == "U(1)"
    assert packet["A_field_domain_policy"] == A_FIELD_DOMAIN_POLICY
    assert packet["F_definition_policy"] == F_DEFINITION_POLICY
    assert packet["derivative_convention_policy"] == DERIVATIVE_CONVENTION_POLICY
    assert packet["variation_policy"] == VARIATION_POLICY
    assert packet["pure_gauge_equation_route"] == PURE_GAUGE_EQUATION_ROUTE
    assert packet["current_route_shape"] == CURRENT_ROUTE_SHAPE
    assert packet["current_policy"] == CURRENT_POLICY
    assert packet["gauge_fixing_policy"] == GAUGE_FIXING_POLICY
    assert packet["ck_role_policy"] == CK_ROLE_POLICY
    assert POLICY_ITEMS == [
        "gauge group",
        "A field/domain policy",
        "definition of F",
        "ordinary vs gauge-covariant derivative",
        "boundary variation policy",
        "pure gauge equation route",
        "current policy",
        "gauge fixing status",
        "A-relevant C_k role",
    ]


def test_a_gauge_policy_packet_retains_expected_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["review_criteria_count"] == 13
    assert packet["review_criteria_accepted_count"] == 13
    assert {row["row_id"] for row in packet["review_criteria"]} == {
        "consumes_expected_gauge_policy_packet_target",
        "u1_abelian_route_selected",
        "A_smooth_real_one_form_domain_selected",
        "F_definition_selected",
        "abelian_derivative_convention_selected",
        "boundary_variation_policy_selected",
        "pure_gauge_vacuum_route_recorded",
        "current_route_shape_recorded_derivation_blocked",
        "external_current_not_selected_as_native_derivation",
        "psi_derived_current_deferred",
        "nonabelian_route_not_selected",
        "gauge_fixing_not_selected_as_physical_structure",
        "no_derivation_closure_or_promotion",
    }
    assert packet["vacuum_variation_retry_authorized"] is True
    assert packet["vacuum_variation_retry_executed"] is False
    assert packet["native_derivation_blocked"] is True
    for key in [
        "nonabelian_route_selected",
        "gauge_covariant_D_mu_route_selected",
        "covariant_derivative_D_mu_convention_selected",
        "boundary_terms_controlled",
        "current_route_derived",
        "external_current_policy_selected",
        "matter_current_J_nu_derived",
        "gauge_fixing_selected",
        "gauge_fixing_selected_as_physical_structure",
        "C_k_analogues_constructed",
        "A_relevant_C_k_rules_constructed",
        "source_bridge_transport_ck_analogues_constructed",
        "formal_theorem_backed_gauge_derivation",
        "a_surface_variation_executed",
        "a_surface_variation_route_executed",
        "maxwell_equation_derived",
        "maxwell_equations_derived",
        "yang_mills_equations_derived",
        "field_equations_derived",
        "gauge_field_derived",
        "current_source_route_constructed",
        "current_conservation_proved",
        "gauge_current_constraint_proved",
        "stress_energy_T_A_derived",
        "stress_energy_route_constructed",
        "stress_energy_source_admissibility_proved",
        "A_source_admissibility_proved",
        "source_admissibility_proved",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_map_closed",
        "qft_gr_solved",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "em_closure_claimed",
        "em_qft_closure_claimed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
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
    for phrase in [
        "minimal Abelian U(1) test route only",
        "does not derive Maxwell equations",
        "does not derive J^nu",
        "does not prove current conservation",
        "does not select gauge fixing as physical structure",
        "does not select a non-Abelian route",
        "does not derive stress-energy T_A",
        "does not prove A-source admissibility",
        "does not construct A-relevant C_k rules",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_gauge_policy_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_gauge_policy_packet_rotates_live_target_to_vacuum_retry() -> None:
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
        "ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_20260621_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["a_gauge_policy_packet_result"] == A_GAUGE_POLICY_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["u1_route_selected"] == "yes"
    assert consumed["current_derivation_blocked"] == "yes"
    assert consumed["maxwell_equations_derived"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["a_gauge_policy_decision"] == A_GAUGE_POLICY_DECISION
    assert active_row["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert active_row["selected_gauge_group"] == "U(1)"
    assert active_row["definition_of_F_selected"] == "yes"
    assert active_row["current_derivation_blocked"] == "yes"
    assert active_row["external_current_policy_selected"] == "no"
    assert active_row["psi_derived_current_deferred"] == "yes"
    assert active_row["A_relevant_C_k_rules_constructed"] == "no"
    assert active_row["em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_gauge_policy_packet_lean_and_surface_mirrors() -> None:
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
        A_GAUGE_POLICY_DECISION,
        A_GAUGE_POLICY_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DEFERRED_CURRENT_POLICY_TARGET,
        DEFERRED_A_CK_RULE_TARGET,
        "ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_vacuum_variation_retry_under_selected_u1_policy",
        "U(1) / Abelian test route",
        "smooth real 1-form",
        "F = dA",
        "compact-support or fixed-boundary variation",
        "current derivation blocked",
        "psi-derived current deferred",
        "external current not selected as native derivation",
        "Maxwell/Yang-Mills derivation",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert token in joined


def test_a_gauge_policy_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_gauge_group_domain_and_current_policy_packet_gate.py"
    )
