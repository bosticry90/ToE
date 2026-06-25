from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.toe_native_psi_a_u1_current_conservation_obligation_packet_report import (
    ADJOINT_DIRAC_ROUTE_OBLIGATION,
    ALTERNATE_NEXT_TARGET,
    BLOCKED_CLAIMS,
    BOUNDED_ROUTE_SHAPE,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CANDIDATE_POLICY,
    CURRENT_REVIEW_OUTCOME,
    CURRENT_REVIEW_PATH,
    DEFAULT_OUT,
    DIRAC_ROUTE_EQUATION,
    FIELD_EQUATION_ROUTE_PREVIEW,
    GAUGE_SYMMETRY_ROUTE_PREVIEW,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATIONS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PROOF_ROUTES,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
    TARGET_CONSERVATION_LAW,
    build_toe_native_psi_a_u1_current_conservation_obligation_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_current_conservation_obligation_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
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
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_psi_a_u1_current_conservation_obligation_packet_files_exist() -> None:
    for path in [
        CURRENT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_current_conservation_obligation_packet_consumes_current_review() -> None:
    review = _json(CURRENT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == CURRENT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["consumed_current_derivation_result_review"] == CURRENT_REVIEW_OUTCOME
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["alternate_next_target"] == ALTERNATE_NEXT_TARGET
    assert build_toe_native_psi_a_u1_current_conservation_obligation_packet() == packet


def test_psi_a_u1_current_conservation_obligation_packet_indexes_requirements_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["target_conservation_law"] == TARGET_CONSERVATION_LAW
    assert packet["current_candidate_policy"] == CURRENT_CANDIDATE_POLICY
    assert packet["current_candidate_from_A_variation"] == CURRENT_CANDIDATE_FROM_A_VARIATION
    assert packet["bounded_route_shape"] == BOUNDED_ROUTE_SHAPE
    assert packet["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert packet["proof_routes"] == PROOF_ROUTES
    assert packet["proof_route_count"] == 3
    assert packet["obligations"] == OBLIGATIONS
    assert packet["obligation_count"] == 6
    assert packet["gauge_symmetry_route_preview"] == GAUGE_SYMMETRY_ROUTE_PREVIEW
    assert packet["field_equation_route_preview"] == FIELD_EQUATION_ROUTE_PREVIEW
    assert (
        packet["sourced_maxwell_consistency_route_preview"]
        == SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW
    )
    assert packet["dirac_route_equation"] == DIRAC_ROUTE_EQUATION
    assert packet["adjoint_dirac_route_obligation"] == ADJOINT_DIRAC_ROUTE_OBLIGATION
    for key in [
        "current_conservation_obligation_packet_prepared",
        "current_conservation_requirements_indexed",
        "current_candidate_preserved",
        "target_conservation_law_indexed",
        "proof_routes_indexed",
        "gauge_symmetry_route_indexed",
        "field_equation_route_indexed",
        "sourced_maxwell_consistency_route_indexed",
        "field_equation_route_selected_as_next",
        "psi_variation_dirac_route_packet_selected",
        "psi_variation_dirac_route_packet_preparation_authorized",
    ]:
        assert packet[key] is True, key
    assert packet["current_conservation_route_executed"] is False


def test_psi_a_u1_current_conservation_obligation_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 15
    for key in [
        "current_conservation_proved",
        "psi_variation_result_derived",
        "psi_field_equation_derived",
        "dirac_equation_derived",
        "adjoint_dirac_equation_derived",
        "sourced_maxwell_closure_claimed",
        "sourced_maxwell_equation_derived",
        "stress_energy_derived",
        "psi_stress_energy_derived",
        "exchange_identity_proved",
        "gauge_matter_exchange_proved",
        "matter_gauge_exchange_proved",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "current-conservation obligation packet only",
        "nabla_mu J^mu = 0",
        "J^mu = q psibar gamma^mu psi",
        "no current conservation proof",
        "no psi variation or Dirac derivation",
        "no adjoint Dirac derivation",
        "no sourced Maxwell closure",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_current_conservation_obligation_packet_rotates_to_dirac_route() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == str(
        LEAN_PACKET_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["live_next_target_report"] == str(
        DEFAULT_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert state["live_next_target_kind"] == NEXT_TARGET_KIND
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["current_conservation_obligation_packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["target_conservation_law"] == TARGET_CONSERVATION_LAW
    assert consumed["proof_routes_indexed"] == "yes"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["dirac_equation_derived"] == "no"
    assert consumed["adjoint_dirac_equation_derived"] == "no"
    assert consumed["sourced_maxwell_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["consumed_current_conservation_obligation_packet_result"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["psi_variation_dirac_route_packet_result"] == "PENDING"
    assert active_row["psi_variation_dirac_route_packet_preparation_authorized"] == "yes"
    assert active_row["psi_variation_dirac_route_packet_prepared"] == "no"
    assert active_row["target_conservation_law"] == TARGET_CONSERVATION_LAW
    assert active_row["current_candidate_policy"] == CURRENT_CANDIDATE_POLICY
    assert active_row["proof_route_count"] == "3"
    assert active_row["dirac_route_equation"] == DIRAC_ROUTE_EQUATION
    assert active_row["adjoint_dirac_route_obligation"] == ADJOINT_DIRAC_ROUTE_OBLIGATION
    for key in [
        "current_conservation_obligation_packet_prepared",
        "current_conservation_requirements_indexed",
        "current_candidate_preserved",
        "target_conservation_law_indexed",
        "proof_routes_indexed",
        "gauge_symmetry_route_indexed",
        "field_equation_route_indexed",
        "sourced_maxwell_consistency_route_indexed",
        "field_equation_route_selected_as_next",
        "psi_variation_dirac_route_packet_selected",
    ]:
        assert active_row[key] == "yes", key
    for key in [
        "current_conservation_proved",
        "psi_variation_result_derived",
        "psi_field_equation_derived",
        "dirac_equation_derived",
        "adjoint_dirac_equation_derived",
        "sourced_maxwell_closure_claimed",
        "sourced_maxwell_equation_derived",
        "stress_energy_derived",
        "exchange_identity_proved",
        "total_conservation_proved",
        "C_exchange_definition_closeout",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert active_row[key] == "no", key


def test_psi_a_u1_current_conservation_obligation_packet_lean_and_surface_mirrors() -> None:
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
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CurrentConservationObligationPacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_psi_variation_dirac_route_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_conservation_obligation_packet",
        TARGET_CONSERVATION_LAW,
        CURRENT_CANDIDATE_POLICY,
        GAUGE_SYMMETRY_ROUTE_PREVIEW,
        FIELD_EQUATION_ROUTE_PREVIEW,
        SOURCED_MAXWELL_CONSISTENCY_ROUTE_PREVIEW,
        DIRAC_ROUTE_EQUATION,
        "no current conservation proof",
        "no psi variation or Dirac derivation",
        "no adjoint Dirac derivation",
        "no sourced Maxwell closure",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_current_conservation_obligation_packet_validation_policy_is_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_current_conservation_obligation_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_current_conservation_obligation_packet_gate.py"
    )
