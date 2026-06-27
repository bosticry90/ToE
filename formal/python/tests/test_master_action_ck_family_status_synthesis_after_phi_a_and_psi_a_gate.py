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
from formal.python.tools.master_action_ck_family_status_synthesis_after_phi_a_and_psi_a_report import (
    A_CLOSEOUT_OUTCOME,
    A_CLOSEOUT_PATH,
    ARTIFACT_ID,
    C_BRIDGE_CLASSIFICATION,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CLASSIFICATION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_SOURCE_CLASSIFICATION,
    C_TRANSPORT_CLASSIFICATION,
    CONSUMED_TARGET,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_CLOSEOUT_OUTCOME,
    PHI_CLOSEOUT_PATH,
    PSI_A_CLOSEOUT_RESULT_REVIEW_OUTCOME,
    PSI_A_CLOSEOUT_RESULT_REVIEW_PATH,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_OUTCOME_HINT,
    SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    build_master_action_ck_family_status_synthesis_after_phi_a_and_psi_a,
)
from formal.python.tools.master_action_ck_family_status_synthesis_result_review_report import (
    DEFAULT_OUT as SYNTHESIS_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as SYNTHESIS_RESULT_REVIEW_NEXT_TARGET,
    NEXT_TARGET_KIND as SYNTHESIS_RESULT_REVIEW_NEXT_TARGET_KIND,
    OUTCOME_ID as SYNTHESIS_RESULT_REVIEW_OUTCOME,
    RECOMMENDED_SELECTOR_CHOICE as SYNTHESIS_RESULT_REVIEW_RECOMMENDED_SELECTOR_CHOICE,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_family_status_synthesis_after_phi_a_and_psi_a_report.py"
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


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_master_action_ck_family_status_synthesis_files_exist() -> None:
    for path in [
        PHI_CLOSEOUT_PATH,
        A_CLOSEOUT_PATH,
        PSI_A_CLOSEOUT_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_master_action_ck_family_status_synthesis_accepts_prior_packets() -> None:
    phi_closeout = _json(PHI_CLOSEOUT_PATH)
    a_closeout = _json(A_CLOSEOUT_PATH)
    psi_a_review = _json(PSI_A_CLOSEOUT_RESULT_REVIEW_PATH)
    payload = _json(DEFAULT_OUT)

    assert phi_closeout["outcome_id"] == PHI_CLOSEOUT_OUTCOME
    assert a_closeout["outcome_id"] == A_CLOSEOUT_OUTCOME
    assert psi_a_review["outcome_id"] == PSI_A_CLOSEOUT_RESULT_REVIEW_OUTCOME

    assert payload["artifact_id"] == ARTIFACT_ID
    assert payload["schema_id"] == SCHEMA_ID
    assert payload["packet_id"] == PACKET_ID
    assert payload["prepared"] is True
    assert payload["accepted"] is True
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["packet_result"] == OUTCOME_ID
    assert payload["packet_classification"] == PACKET_CLASSIFICATION
    assert payload["consumed_target"] == CONSUMED_TARGET
    assert payload["selected_next_target"] == NEXT_TARGET
    assert payload["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert payload["review_outcome_hint"] == REVIEW_OUTCOME_HINT
    assert build_master_action_ck_family_status_synthesis_after_phi_a_and_psi_a() == (
        payload
    )


def test_master_action_ck_family_status_synthesis_classifies_rule_families() -> None:
    payload = _json(DEFAULT_OUT)
    assert payload["family_count"] == 3
    assert payload["isolated_field_family_count"] == 2
    assert payload["interaction_family_count"] == 1
    assert payload["mature_rule_class_count"] == 4
    assert payload["C_source_classification"] == C_SOURCE_CLASSIFICATION
    assert payload["C_bridge_classification"] == C_BRIDGE_CLASSIFICATION
    assert payload["C_transport_classification"] == C_TRANSPORT_CLASSIFICATION
    assert payload["C_exchange_classification"] == C_EXCHANGE_CLASSIFICATION
    assert [row["family_id"] for row in payload["family_status_summary"]] == [
        "phi",
        "A",
        "psi-A",
    ]
    for key in [
        "synthesis_packet_prepared",
        "synthesis_packet_accepted",
        "master_action_ck_family_status_synthesis_prepared",
        "ck_family_status_synthesis_prepared",
        "phi_source_bridge_transport_family_synthesized",
        "A_source_bridge_transport_family_synthesized",
        "psi_A_interaction_exchange_family_synthesized",
        "C_source_classified",
        "C_bridge_classified",
        "C_transport_classified",
        "C_exchange_classified",
        "isolated_field_rule_families_summarized",
        "interaction_rule_family_summarized",
        "admissibility_rule_architecture_summary_prepared",
    ]:
        assert payload[key] is True, key
    for token in [
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
    ]:
        assert token in payload["mathematical_statement"], token


def test_master_action_ck_family_status_synthesis_preserves_nonclaims_and_not_run() -> None:
    payload = _json(DEFAULT_OUT)
    for key in [
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "multiplier_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "full_maxwell_closure_claimed",
        "full_Maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "master_action_promotion",
        "seam_closure_claim",
        "ck_family_status_synthesis_result_review_prepared",
    ]:
        assert payload[key] is False, key
    for phrase in [
        "admissibility-only",
        "not action embedded",
        "not varied",
        "not direct dynamical laws",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical, non-promoted organizing surface",
        "full ToeFormal aggregate is kept as NOT_RUN",
    ]:
        assert phrase in payload["non_claim_boundary"], phrase
    assert payload["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert payload["full_toeformal_aggregate_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert payload["full_toeformal_aggregate_passed"] is False
    assert payload["full_toeformal_aggregate_failed"] is False
    assert payload["full_toeformal_aggregate_timed_out"] is False


def test_master_action_ck_family_status_synthesis_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["master_action_ck_family_status_synthesis_prepared"] == "yes"
    assert consumed["ck_family_status_synthesis_prepared"] == "yes"
    if is_current:
        assert NEXT_TARGET not in registry["completed_targets"]
        assert NEXT_TARGET not in registry["consumed_targets"]
        assert NEXT_TARGET not in registry["paused_lanes"]
        assert consumed["ck_family_status_synthesis_result_review_prepared"] == "no"
        active_row = _workstream(registry, NEXT_TARGET)
        assert active_row["status"] == "active"
        assert active_row["workstream_id"] == NEXT_TARGET
        assert active_row["active_lane"] == NEXT_TARGET
        assert active_row["authorized_next_strict_target"] == NEXT_TARGET
        assert active_row["authorized_target"] == NEXT_TARGET
        assert active_row["authorization_evidence"] == evidence
        assert active_row["report"] == _rel(DEFAULT_OUT)
        assert active_row["consumed_target"] == CONSUMED_TARGET
        assert active_row["packet_result"] == "PENDING"
        assert active_row["review_result"] == "PENDING"
        assert active_row["result_review_prepared"] == "no"
        assert active_row["outcome_id"] == OUTCOME_ID
        assert active_row["result_token"] == OUTCOME_ID
        assert active_row["selected_next_target"] == NEXT_TARGET
        assert active_row["selected_next_target_kind"] == NEXT_TARGET_KIND
        assert active_row["master_action_ck_family_status_synthesis_prepared"] == "yes"
        assert active_row["ck_family_status_synthesis_prepared"] == "yes"
        assert active_row["C_k_action_variation_executed"] == "no"
        assert active_row["em_qft_closure_claimed"] == "no"
        assert active_row["qft_gr_closure_claimed"] == "no"
        assert active_row["gr_qm_closure_claimed"] == "no"
        assert active_row["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
        review_row = _workstream(registry, NEXT_TARGET)
        assert review_row["status"] == "paused"
        assert review_row["authorization_evidence"] == _rel(
            SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH
        )
        assert review_row["report"] == _rel(SYNTHESIS_RESULT_REVIEW_OUT)
        assert review_row["packet_result"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
        assert review_row["review_result"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
        assert review_row["outcome_id"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
        assert review_row["result_token"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
        assert review_row["selected_next_target"] == (
            SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
        )
        assert review_row["selected_next_target_kind"] == (
            SYNTHESIS_RESULT_REVIEW_NEXT_TARGET_KIND
        )
        assert review_row["master_action_surface_selector_authorized"] == "yes"
        assert review_row["master_action_surface_selector_executed"] == "no"
        assert review_row["master_action_surface_selected"] == "no"

        selector_row = _workstream(registry, SYNTHESIS_RESULT_REVIEW_NEXT_TARGET)
        if selector_row["status"] == "active":
            assert selector_row["workstream_id"] == SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
            assert selector_row["active_lane"] == SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
            assert selector_row["authorized_next_strict_target"] == (
                SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
            )
            assert selector_row["authorized_target"] == SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
            assert selector_row["authorization_evidence"] == _rel(
                SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH
            )
            assert selector_row["report"] == _rel(SYNTHESIS_RESULT_REVIEW_OUT)
            assert selector_row["consumed_target"] == NEXT_TARGET
            assert selector_row["packet_result"] == "PENDING"
            assert selector_row["review_result"] == "PENDING"
            assert selector_row["outcome_id"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
            assert selector_row["selected_next_target"] == (
                SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
            )
            assert selector_row["selected_next_target_kind"] == (
                SYNTHESIS_RESULT_REVIEW_NEXT_TARGET_KIND
            )
            assert selector_row["recommended_selector_choice"] == (
                SYNTHESIS_RESULT_REVIEW_RECOMMENDED_SELECTOR_CHOICE
            )
            assert selector_row["master_action_surface_selector_authorized"] == "yes"
            assert selector_row["master_action_surface_selector_executed"] == "no"
            assert selector_row["master_action_surface_selected"] == "no"
        else:
            gap_target = "prepare_master_action_ck_family_gap_review_after_phi_A_and_psi_A"
            assert selector_row["status"] == "paused"
            assert selector_row["selected_next_target"] == gap_target
            assert selector_row["master_action_surface_selector_executed"] == "yes"
            assert selector_row["master_action_surface_selected"] == "yes"
            assert selector_row["ck_family_gap_review_selected"] == "yes"
            gap_row = _workstream(registry, gap_target)
            if gap_row["status"] == "active":
                assert gap_row["consumed_target"] == SYNTHESIS_RESULT_REVIEW_NEXT_TARGET
                assert gap_row["selected_next_target"] == gap_target
                assert gap_row["ck_family_gap_review_prepared"] == "no"
            else:
                gap_review_target = (
                    "review_master_action_ck_family_gap_review_after_phi_A_and_psi_A_result"
                )
                assert gap_row["status"] == "paused"
                assert gap_row["selected_next_target"] == gap_review_target
                assert gap_row["gap_review_prepared"] == "yes"
                assert str(gap_row["gap_count"]) == "8"
                active_gap_review = _workstream(registry, gap_review_target)
                assert active_gap_review["status"] == "active"
                assert active_gap_review["consumed_target"] == gap_target
                assert active_gap_review["gap_review_prepared"] == "yes"
                assert active_gap_review["result_review_prepared"] == "no"


def test_master_action_ck_family_status_synthesis_mirrors() -> None:
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
        "MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiA",
        CONSUMED_TARGET,
        NEXT_TARGET,
        SYNTHESIS_RESULT_REVIEW_NEXT_TARGET,
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_NONCLAIM_BOUNDARY_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        C_SOURCE_CLASSIFICATION,
        C_BRIDGE_CLASSIFICATION,
        C_TRANSPORT_CLASSIFICATION,
        C_EXCHANGE_CLASSIFICATION,
        CURRENT_CANDIDATE,
        SOURCED_GAUGE_ROUTE,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_master_action_ck_family_status_synthesis_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_family_status_synthesis_after_phi_a_and_psi_a_gate.py"
    )
