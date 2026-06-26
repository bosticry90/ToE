from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.toe_native_psi_a_u1_gauge_sector_exchange_route_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    CURRENT_CONSERVATION_RESULT,
    DEFAULT_OUT,
    FIELD_STRENGTH_POLICY,
    FULL_TOEFORMAL_AGGREGATE_ATTEMPT_NOTE,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_DIVERGENCE_INTERMEDIATE,
    GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION,
    GAUGE_PACKET_OUTCOME,
    GAUGE_PACKET_PATH,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    GAUGE_STRESS_ENERGY_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_TARGET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    TARGETED_LEAN_BUILD_STATUS,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    build_toe_native_psi_a_u1_gauge_sector_exchange_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_gauge_sector_exchange_route_result_review_report.py"
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


def test_psi_a_u1_gauge_sector_exchange_route_result_review_files_exist() -> None:
    for path in [
        GAUGE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_gauge_sector_exchange_route_result_review_accepts_packet() -> None:
    packet = _json(GAUGE_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == GAUGE_PACKET_OUTCOME
    assert packet["selected_next_target"] == CONSUMED_TARGET

    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_toe_native_psi_a_u1_gauge_sector_exchange_route_result_review()
        == review
    )


def test_psi_a_u1_gauge_sector_exchange_route_result_review_accepts_gauge_side_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 4
    assert review["gauge_stress_energy_policy"] == GAUGE_STRESS_ENERGY_POLICY
    assert review["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert review["sourced_maxwell_route"] == SOURCED_GAUGE_ROUTE
    assert review["source_current"] == SOURCE_CURRENT
    assert review["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert review["field_strength_policy"] == FIELD_STRENGTH_POLICY
    assert review["gauge_divergence_intermediate"] == GAUGE_DIVERGENCE_INTERMEDIATE
    assert (
        review["gauge_divergence_source_substitution"]
        == GAUGE_DIVERGENCE_SOURCE_SUBSTITUTION
    )
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    assert review["matter_sector_exchange_target"] == MATTER_SECTOR_EXCHANGE_TARGET
    assert review["matter_sector_route_to_test"] == MATTER_SECTOR_EXCHANGE_TARGET
    assert (
        review["total_conservation_expanded_target"]
        == TOTAL_CONSERVATION_EXPANDED_TARGET
    )
    for key in [
        "gauge_sector_exchange_route_result_review_accepted",
        "gauge_sector_exchange_route_accepted",
        "gauge_stress_energy_divergence_route_recorded",
        "sourced_maxwell_route_used_as_input",
        "J_current_candidate_used_as_input",
        "gauge_sector_exchange_identity_recorded",
        "gauge_sector_exchange_identity_accepted",
        "gauge_side_exchange_only",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_gauge_sector_exchange_route_result_review_selects_matter_route() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["matter_sector_exchange_route_packet_selected"] is True
    assert review["matter_sector_exchange_route_packet_preparation_authorized"] is True
    assert review["total_conservation_future_combination"] == (
        "nabla_mu T_A^{mu nu} + nabla_mu T_psi^{mu nu} = 0"
    )
    assert review["total_conservation_packet_selected"] is False
    assert review["total_conservation_packet_authorized_here"] is False


def test_psi_a_u1_gauge_sector_exchange_route_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 12
    for key in [
        "matter_sector_exchange_proved",
        "matter_sector_exchange_route_constructed",
        "matter_sector_exchange_identity_recorded",
        "gauge_matter_exchange_identity_proved",
        "exchange_identity_proved",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "C_exchange_rule_family_closed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert review[key] is False, key
    for phrase in [
        "gauge-sector exchange route result review only",
        "no matter-sector exchange proof",
        "no total conservation proof",
        "no C_exchange closeout",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_gauge_sector_exchange_route_result_review_records_aggregate_status() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["targeted_lean_build_status_for_review"] == TARGETED_LEAN_BUILD_STATUS
    assert policy["targeted_lean_builds_passed"] is True
    assert policy["aggregate_lean_validation_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_attempt_note"] == (
        FULL_TOEFORMAL_AGGREGATE_ATTEMPT_NOTE
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert policy["full_toeformal_aggregate_stopped_manually"] is True
    assert review["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_stopped_manually"] is True


def test_psi_a_u1_gauge_sector_exchange_route_result_review_rotates_to_matter_packet() -> None:
    registry = _json(REGISTRY_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        lane=NEXT_TARGET,
    )
    if is_current:
        assert_current_target_consistent()
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()

    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    if is_current:
        assert state["previous_live_next_target"] == CONSUMED_TARGET
        assert state["live_next_target"] == NEXT_TARGET
        assert state["active_lane"] == NEXT_TARGET
        assert state["live_next_target_evidence"] == str(
            LEAN_PACKET_PATH.relative_to(REPO_ROOT)
        ).replace("\\", "/")
        assert (
            state["live_next_target_report"]
            == "formal/docs/release/"
            "TOE_NATIVE_PSI_A_U1_GAUGE_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
            "20260625_v0.json"
        )
        assert state["live_next_target_outcome"] == OUTCOME_ID

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["gauge_sector_exchange_route_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert consumed["gauge_sector_exchange_route_packet_result_review_completed"] == (
        "yes"
    )
    assert consumed["matter_sector_exchange_route_packet_selected"] == "yes"
    assert consumed["matter_sector_exchange_route_packet_preparation_authorized"] == (
        "yes"
    )
    assert consumed["matter_sector_exchange_route_constructed"] == "no"
    assert consumed["total_conservation_proved"] == "no"
    assert consumed["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )

    next_row = _workstream(registry, NEXT_TARGET)
    assert next_row["workstream_id"] == NEXT_TARGET
    if is_current:
        assert next_row["status"] == "active"
        assert next_row["active_lane"] == NEXT_TARGET
        assert next_row["authorized_next_strict_target"] == NEXT_TARGET
        assert next_row["authorized_target"] == NEXT_TARGET
        assert next_row["authorization_evidence"] == str(
            LEAN_PACKET_PATH.relative_to(REPO_ROOT)
        ).replace("\\", "/")
        assert next_row["consumed_target"] == CONSUMED_TARGET
        assert next_row["gauge_sector_exchange_route_packet_result_review_result"] == (
            OUTCOME_ID
        )
        assert next_row["packet_result"] == "PENDING"
        assert next_row["matter_sector_exchange_route_packet_result"] == "PENDING"
        assert next_row["matter_sector_exchange_route_constructed"] == "no"
        assert next_row["total_conservation_proved"] == "no"
    else:
        matter_packet_outcome = (
            "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_PACKET_PREPARED_"
            "MATTER_SECTOR_EXCHANGE_ROUTE_CONSTRUCTED_NO_TOTAL_CONSERVATION_OR_"
            "CEXCHANGE_CLOSURE"
        )
        assert next_row["status"] == "paused"
        assert next_row["packet_result"] == matter_packet_outcome
        assert next_row["matter_sector_exchange_route_packet_result"] == (
            matter_packet_outcome
        )
        assert next_row["matter_sector_exchange_route_constructed"] == "yes"
        assert next_row["matter_sector_exchange_identity_recorded"] == "yes"
        assert next_row["total_conservation_proved"] == "no"


def test_psi_a_u1_gauge_sector_exchange_route_result_review_mirrors() -> None:
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
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1GaugeSectorExchangeRouteResultReview",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_toe_native_psi_A_u1_matter_sector_exchange_route_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: review_toe_native_psi_A_u1_gauge_sector_exchange_route_packet_result",
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        SOURCED_GAUGE_ROUTE,
        SOURCE_CURRENT,
        "Targeted Lean builds passed",
        FULL_TOEFORMAL_AGGREGATE_STATUS,
        "no matter-sector exchange proof",
        "no total conservation proof",
        "no C_exchange closeout",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined


def test_psi_a_u1_gauge_sector_exchange_route_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_gauge_sector_exchange_route_result_review_gate.py"
    )
