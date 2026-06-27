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
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ARTIFACT_ID,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_OUTCOME_HINT,
    CONSUMED_TARGET,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    RULE_FAMILY_ID,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    SYNTHESIS_PACKET_OUTCOME,
    SYNTHESIS_PACKET_PATH,
    SYNTHESIS_PACKET_RESULT,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review,
)
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_report import (
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_REVIEW_TARGET,
    NEXT_TARGET_KIND as CLOSEOUT_REVIEW_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
)
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_report import (
    DEFAULT_OUT as CLOSEOUT_REVIEW_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as CK_FAMILY_STATUS_SYNTHESIS_TARGET,
    NEXT_TARGET_KIND as CK_FAMILY_STATUS_SYNTHESIS_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_REVIEW_OUTCOME,
)
from formal.python.tools.master_action_ck_family_status_synthesis_after_phi_a_and_psi_a_report import (
    DEFAULT_OUT as CK_FAMILY_STATUS_SYNTHESIS_OUT,
    LEAN_PACKET_PATH as CK_FAMILY_STATUS_SYNTHESIS_LEAN_PACKET_PATH,
    NEXT_TARGET as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET,
    NEXT_TARGET_KIND as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET_KIND,
    OUTCOME_ID as CK_FAMILY_STATUS_SYNTHESIS_OUTCOME,
)
from formal.python.tools.master_action_ck_family_status_synthesis_result_review_report import (
    DEFAULT_OUT as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET,
    OUTCOME_ID as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review_report.py"
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


def test_psi_a_u1_interaction_exchange_synthesis_result_review_files_exist() -> None:
    for path in [
        SYNTHESIS_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_interaction_exchange_synthesis_result_review_accepts_packet() -> None:
    packet = _json(SYNTHESIS_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == SYNTHESIS_PACKET_OUTCOME
    assert packet["packet_result"] == SYNTHESIS_PACKET_RESULT
    assert packet["selected_next_target"] == CONSUMED_TARGET

    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["closeout_outcome_hint"] == CLOSEOUT_OUTCOME_HINT
    assert build_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review() == review


def test_psi_a_u1_interaction_exchange_synthesis_result_review_preserves_chain() -> None:
    review = _json(DEFAULT_OUT)
    assert review["rule_family_id"] == RULE_FAMILY_ID
    assert review["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert review["rule_family_epistemic_status"] == RULE_FAMILY_EPISTEMIC_STATUS
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 7
    assert review["route_family_chain_count"] == 7
    assert [row["route_id"] for row in review["route_family_chain"]] == [
        "A_variation_current_candidate",
        "current_conservation",
        "sourced_maxwell_route",
        "gauge_sector_exchange",
        "matter_sector_exchange",
        "total_stress_energy_conservation",
        "C_exchange_rule",
    ]
    assert review["current_candidate"] == CURRENT_CANDIDATE
    assert review["source_current"] == SOURCE_CURRENT
    assert review["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert review["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert review["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert review["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert review["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert review["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert review["C_exchange_total_stress_energy_form"] == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    assert review["C_exchange_admissibility_condition"] == C_EXCHANGE_ADMISSIBILITY_CONDITION
    assert review["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert review["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert review["C_exchange_rule_classification"] == RULE_CLASSIFICATION
    assert review["C_exchange_rule_epistemic_status"] == RULE_EPISTEMIC_STATUS


def test_psi_a_u1_interaction_exchange_synthesis_result_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "synthesis_packet_consumed",
        "psi_A_current_route_synthesized",
        "current_conservation_route_synthesized",
        "sourced_maxwell_route_synthesized",
        "gauge_sector_exchange_route_synthesized",
        "matter_sector_exchange_route_synthesized",
        "total_stress_energy_conservation_route_synthesized",
        "C_exchange_admissibility_rule_included",
        "no_forbidden_closure_or_action_claims",
        "interaction_exchange_rule_family_closeout_selected",
    }
    assert review["review_criteria_count"] == 10
    assert review["review_criteria_accepted_count"] == 10
    for key in [
        "result_review_prepared",
        "result_review_accepted",
        "synthesis_packet_accepted",
        "psi_A_current_route_synthesized",
        "current_conservation_route_synthesized",
        "sourced_maxwell_route_synthesized",
        "gauge_sector_exchange_route_synthesized",
        "matter_sector_exchange_route_synthesized",
        "total_stress_energy_conservation_route_synthesized",
        "C_exchange_admissibility_rule_included",
        "C_exchange_remains_admissibility_only",
        "current_source_exchange_and_total_conservation_synthesis_accepted",
        "interaction_exchange_rule_family_closeout_authorized",
    ]:
        assert review[key] is True, key
    assert review["interaction_exchange_rule_family_closeout_prepared"] is False


def test_psi_a_u1_interaction_exchange_synthesis_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "functional_action_embedding_claimed",
        "C_exchange_functional_embedding_claimed",
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "candidate_varied",
        "direct_dynamical_law_interpretation_selected",
        "direct_force_law_claimed",
        "new_force_law_claimed",
        "full_maxwell_closure_claimed",
        "full_Maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "anomaly_analysis_performed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "pillar_completion_inferred",
        "seam_closure_claim",
        "EM_QFT_closure",
        "QFT_GR_closure",
        "master_action_promotion",
    ]:
        assert review[key] is False, key


def test_psi_a_u1_interaction_exchange_synthesis_result_review_nonclaim_boundary() -> None:
    boundary = _json(DEFAULT_OUT)["non_claim_boundary"]
    for phrase in [
        "accepts only the psi-A current route",
        "current conservation route",
        "sourced Maxwell route",
        "gauge-sector exchange route",
        "matter-sector exchange route",
        "total stress-energy conservation route",
        "C_exchange admissibility rule inclusion",
        "no C_k action embedding",
        "no C_k action variation",
        "no multiplier/action route",
        "no penalty route",
        "no direct dynamical-law interpretation",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical organizing surface",
    ]:
        assert phrase in boundary, phrase


def test_psi_a_u1_interaction_exchange_synthesis_result_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_interaction_exchange_synthesis_result_review_rotates_to_closeout() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = str(LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
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
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["result_review_prepared"] == "yes"
    assert consumed["interaction_exchange_rule_family_synthesis_packet_prepared"] == "yes"
    assert consumed["interaction_exchange_rule_family_synthesized"] == "yes"
    assert consumed["current_source_exchange_and_total_conservation_routes_synthesized"] == (
        "yes"
    )
    assert consumed["C_exchange_admissibility_rule_included"] == "yes"
    assert consumed["C_exchange_remains_admissibility_only"] == "yes"
    assert consumed["functional_action_embedding_claimed"] == "no"
    assert consumed["multiplier_action_route_selected"] == "no"
    assert consumed["penalty_route_selected"] == "no"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    closeout_row = _workstream(registry, NEXT_TARGET)
    assert closeout_row["workstream_id"] == NEXT_TARGET
    assert closeout_row["closeout_outcome_hint"] == CLOSEOUT_OUTCOME_HINT
    assert closeout_row["interaction_exchange_rule_family_synthesis_result_review_result"] == (
        OUTCOME_ID
    )
    assert closeout_row["interaction_exchange_rule_family_synthesis_packet_prepared"] == "yes"
    assert closeout_row["interaction_exchange_rule_family_synthesized"] == "yes"
    assert closeout_row["current_source_exchange_and_total_conservation_routes_synthesized"] == (
        "yes"
    )
    assert closeout_row["current_source_exchange_and_total_conservation_synthesis_accepted"] == (
        "yes"
    )
    assert closeout_row["C_exchange_admissibility_rule_included"] == "yes"
    assert closeout_row["C_exchange_remains_admissibility_only"] == "yes"
    assert closeout_row["multiplier_action_route_selected"] == "no"
    assert closeout_row["penalty_route_selected"] == "no"
    assert closeout_row["C_k_action_variation_executed"] == "no"
    assert closeout_row["em_qft_closure_claimed"] == "no"
    assert closeout_row["qft_gr_closure_claimed"] == "no"
    assert closeout_row["master_action_promoted"] == "no"

    if is_current:
        assert NEXT_TARGET not in registry["completed_targets"]
        assert NEXT_TARGET not in registry["consumed_targets"]
        assert NEXT_TARGET not in registry["paused_lanes"]
        assert closeout_row["status"] == "active"
        assert closeout_row["active_lane"] == NEXT_TARGET
        assert closeout_row["authorized_next_strict_target"] == NEXT_TARGET
        assert closeout_row["authorized_target"] == NEXT_TARGET
        assert closeout_row["authorization_evidence"] == evidence
        assert closeout_row["report"] == str(DEFAULT_OUT.relative_to(REPO_ROOT)).replace("\\", "/")
        assert closeout_row["consumed_target"] == CONSUMED_TARGET
        assert closeout_row["packet_result"] == "PENDING"
        assert closeout_row["review_result"] == "PENDING"
        assert closeout_row["result_review_prepared"] == "no"
        assert closeout_row["outcome_id"] == OUTCOME_ID
        assert closeout_row["result_token"] == OUTCOME_ID
        assert closeout_row["selected_next_target"] == NEXT_TARGET
        assert closeout_row["selected_next_target_kind"] == NEXT_TARGET_KIND
        assert closeout_row["C_exchange_rule_family_closed"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
        assert closeout_row["status"] == "paused"
        assert closeout_row["authorization_evidence"] == str(
            CLOSEOUT_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
        ).replace("\\", "/")
        assert closeout_row["report"] == str(CLOSEOUT_OUT.relative_to(REPO_ROOT)).replace(
            "\\", "/"
        )
        assert closeout_row["packet_result"] == CLOSEOUT_OUTCOME
        assert closeout_row["closeout_result"] == CLOSEOUT_OUTCOME
        assert closeout_row["outcome_id"] == CLOSEOUT_OUTCOME
        assert closeout_row["result_token"] == CLOSEOUT_OUTCOME
        assert closeout_row["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
        assert closeout_row["selected_next_target_kind"] == CLOSEOUT_REVIEW_TARGET_KIND
        assert closeout_row["interaction_exchange_rule_family_closeout_prepared"] == "yes"
        assert closeout_row["interaction_exchange_rule_family_closed"] == "yes"
        assert closeout_row["C_exchange_rule_family_closed"] == "yes"

        active_row = _workstream(registry, CLOSEOUT_REVIEW_TARGET)
        assert active_row["workstream_id"] == CLOSEOUT_REVIEW_TARGET
        if active_row["status"] == "active":
            assert active_row["outcome_id"] == CLOSEOUT_OUTCOME
            assert active_row["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
            assert active_row["selected_next_target_kind"] == CLOSEOUT_REVIEW_TARGET_KIND
        else:
            assert CLOSEOUT_REVIEW_TARGET in registry["completed_targets"]
            assert CLOSEOUT_REVIEW_TARGET in registry["consumed_targets"]
            assert CLOSEOUT_REVIEW_TARGET in registry["paused_lanes"]
            assert active_row["status"] == "paused"
            assert active_row["authorization_evidence"] == str(
                CLOSEOUT_REVIEW_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
            ).replace("\\", "/")
            assert active_row["report"] == str(CLOSEOUT_REVIEW_OUT.relative_to(REPO_ROOT)).replace(
                "\\", "/"
            )
            assert active_row["packet_result"] == CLOSEOUT_REVIEW_OUTCOME
            assert active_row["review_result"] == CLOSEOUT_REVIEW_OUTCOME
            assert active_row["outcome_id"] == CLOSEOUT_REVIEW_OUTCOME
            assert active_row["selected_next_target"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
            assert active_row["selected_next_target_kind"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET_KIND

            ck_row = _workstream(registry, CK_FAMILY_STATUS_SYNTHESIS_TARGET)
            if ck_row["status"] == "active":
                assert ck_row["workstream_id"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
                assert ck_row["consumed_target"] == CLOSEOUT_REVIEW_TARGET
                assert ck_row["packet_result"] == "PENDING"
                assert ck_row["review_result"] == "PENDING"
                assert ck_row["outcome_id"] == CLOSEOUT_REVIEW_OUTCOME
                assert ck_row["selected_next_target"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
                assert ck_row["selected_next_target_kind"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET_KIND
            else:
                assert ck_row["status"] == "paused"
                assert ck_row["authorization_evidence"] == str(
                    CK_FAMILY_STATUS_SYNTHESIS_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
                ).replace("\\", "/")
                assert ck_row["report"] == str(
                    CK_FAMILY_STATUS_SYNTHESIS_OUT.relative_to(REPO_ROOT)
                ).replace("\\", "/")
                assert ck_row["packet_result"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
                assert ck_row["selected_next_target"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
                assert ck_row["selected_next_target_kind"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET_KIND
                )


def test_psi_a_u1_interaction_exchange_synthesis_result_review_mirrors() -> None:
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
        "ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        CLOSEOUT_REVIEW_TARGET,
        CLOSEOUT_OUTCOME,
        CK_FAMILY_STATUS_SYNTHESIS_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET,
        CLOSEOUT_REVIEW_OUTCOME,
        f"CURRENT_LIVE_NEXT_TARGET_v0: {CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET}",
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET}",
        f"CURRENT_LIVE_TARGET_EVIDENCE_v0: {str(CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH.relative_to(REPO_ROOT)).replace(chr(92), '/')}",
        f"CURRENT_LIVE_TARGET_REPORT_v0: {str(CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUT.relative_to(REPO_ROOT)).replace(chr(92), '/')}",
        f"CURRENT_LIVE_TARGET_OUTCOME_v0: {CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME}",
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCE_CURRENT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        EXCHANGE_TERM_CANCELLATION,
        TOTAL_STRESS_ENERGY_OBJECT,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_ID,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        RULE_FAMILY_ID,
        RULE_FAMILY_CLASSIFICATION,
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no C_k action variation",
        "no master-action promotion",
        "working-form, noncanonical organizing surface",
    ]:
        assert token in joined, token


def test_psi_a_u1_interaction_exchange_synthesis_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review_gate.py"
    )
