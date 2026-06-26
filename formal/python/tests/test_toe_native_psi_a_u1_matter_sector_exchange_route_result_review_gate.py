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
from formal.python.tools.toe_native_psi_a_u1_matter_sector_exchange_route_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRAC_PAIR_ROUTE_INPUTS,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    GAUGE_SECTOR_EXCHANGE_TERM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_DIVERGENCE_CURRENT_SUBSTITUTION,
    MATTER_PACKET_OUTCOME,
    MATTER_PACKET_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    MATTER_SECTOR_EXCHANGE_TERM,
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
    TARGETED_LEAN_BUILD_STATUS,
    TOTAL_CONSERVATION_EXPANDED_TARGET,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_matter_sector_exchange_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_matter_sector_exchange_route_result_review_report.py"
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
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_psi_a_u1_matter_sector_exchange_route_result_review_files_exist() -> None:
    for path in [
        MATTER_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_matter_sector_exchange_route_result_review_accepts_packet() -> None:
    packet = _json(MATTER_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == MATTER_PACKET_OUTCOME
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
        build_toe_native_psi_a_u1_matter_sector_exchange_route_result_review()
        == review
    )


def test_psi_a_u1_matter_sector_exchange_route_result_review_accepts_matter_side_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 4
    assert review["review_criteria_count"] == 8
    assert review["review_criteria_accepted_count"] == 8
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_term"] == MATTER_SECTOR_EXCHANGE_TERM
    assert (
        review["matter_divergence_current_substitution"]
        == MATTER_DIVERGENCE_CURRENT_SUBSTITUTION
    )
    assert review["source_current"] == SOURCE_CURRENT
    assert review["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert review["dirac_pair_route_inputs"] == DIRAC_PAIR_ROUTE_INPUTS
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["gauge_sector_exchange_term"] == GAUGE_SECTOR_EXCHANGE_TERM
    for key in [
        "matter_sector_exchange_route_result_review_accepted",
        "matter_sector_exchange_route_accepted",
        "matter_sector_exchange_route_recorded",
        "matter_sector_exchange_identity_recorded",
        "matter_sector_exchange_identity_accepted",
        "matter_stress_energy_divergence_route_recorded",
        "matter_side_exchange_only",
        "J_alpha_current_candidate_preserved",
        "dirac_pair_current_conservation_context_preserved",
        "gauge_sector_exchange_context_preserved",
        "gauge_sector_exchange_route_accepted",
        "both_exchange_halves_recorded",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_matter_sector_exchange_route_result_review_selects_total_route_without_proving_it() -> None:
    review = _json(DEFAULT_OUT)
    assert review["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert review["total_conservation_expanded_target"] == (
        TOTAL_CONSERVATION_EXPANDED_TARGET
    )
    assert review["total_conservation_route_to_test"] == (
        TOTAL_CONSERVATION_EXPANDED_TARGET
    )
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["ready_for_total_conservation_route_packet"] is True
    assert review["total_conservation_packet_selected"] is True
    assert review["total_conservation_packet_authorized_here"] is True
    assert review["total_stress_energy_conservation_route_packet_selected"] is True
    assert (
        review["total_stress_energy_conservation_route_packet_preparation_authorized"]
        is True
    )
    assert review["total_conservation_proved"] is False
    assert review["total_stress_energy_conservation_proved"] is False


def test_psi_a_u1_matter_sector_exchange_route_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 11
    for key in [
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
        "matter-sector exchange route result review only",
        "J^alpha = q psibar gamma^alpha psi",
        "Dirac-pair/current-conservation context",
        "gauge-sector exchange context",
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
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_matter_sector_exchange_route_result_review_records_validation_scope() -> None:
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
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_matter_sector_exchange_route_result_review_rotates_to_total_packet() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    total_packet_outcome = (
        "TOE_NATIVE_PSI_A_U1_TOTAL_STRESS_ENERGY_CONSERVATION_ROUTE_PACKET_PREPARED_"
        "TOTAL_CONSERVATION_ROUTE_CONSTRUCTED_NO_CEXCHANGE_CLOSEOUT_OR_EM_QFT_CLOSURE"
    )
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
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
        assert state["live_next_target_evidence"] == evidence
        assert (
            state["live_next_target_report"]
            == "formal/docs/release/"
            "TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_"
            "20260625_v0.json"
        )
        assert state["live_next_target_outcome"] == OUTCOME_ID

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["matter_sector_exchange_route_packet_result_review_result"] == (
        OUTCOME_ID
    )
    assert consumed["matter_sector_exchange_route_packet_result_review_completed"] == (
        "yes"
    )
    assert consumed["total_conservation_packet_selected"] == "yes"
    assert consumed["total_conservation_packet_authorized_here"] == "yes"
    assert consumed["total_conservation_proved"] == "no"
    assert consumed["C_exchange_definition_closeout"] == "no"

    next_row = _workstream(registry, NEXT_TARGET)
    assert next_row["workstream_id"] == NEXT_TARGET
    assert next_row["authorized_next_strict_target"] == NEXT_TARGET
    assert next_row["authorized_target"] == NEXT_TARGET
    assert next_row["consumed_target"] == CONSUMED_TARGET
    assert next_row["matter_sector_exchange_route_packet_result_review_result"] == (
        OUTCOME_ID
    )
    if is_current:
        assert next_row["total_stress_energy_conservation_route_packet_result"] == "PENDING"
        assert next_row["total_conservation_route_packet_result"] == "PENDING"
        assert next_row["total_conservation_proved"] == "no"
    else:
        assert next_row["total_stress_energy_conservation_route_packet_result"] == (
            total_packet_outcome
        )
        assert next_row["total_conservation_route_packet_result"] == total_packet_outcome
        assert next_row["total_conservation_proved"] == "yes"
    if is_current:
        assert next_row["status"] == "active"
        assert next_row["active_lane"] == NEXT_TARGET
        assert next_row["packet_result"] == "PENDING"


def test_psi_a_u1_matter_sector_exchange_route_result_review_mirrors() -> None:
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
        "ToeNativePsiAU1MatterSectorExchangeRouteResultReview",
        NEXT_TARGET,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {NEXT_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}",
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        "nabla_mu(T_A^{mu nu} + T_psi^{mu nu}) = 0",
        "Targeted Lean builds passed",
        FULL_TOEFORMAL_AGGREGATE_STATUS,
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


def test_psi_a_u1_matter_sector_exchange_route_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_matter_sector_exchange_route_result_review_gate.py"
    )
