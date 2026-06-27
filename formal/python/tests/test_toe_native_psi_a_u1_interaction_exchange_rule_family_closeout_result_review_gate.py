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
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ARTIFACT_ID,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_OUTCOME,
    CLOSEOUT_PATH,
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
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SOURCED_GAUGE_ROUTE,
    SYNTHESIS_OUTCOME_HINT,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review,
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
    NEXT_TARGET_KIND as CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET_KIND,
    OUTCOME_ID as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_report.py"
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


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_files_exist() -> None:
    for path in [
        CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_accepts_closeout() -> None:
    closeout = _json(CLOSEOUT_PATH)
    review = _json(DEFAULT_OUT)
    assert closeout["outcome_id"] == CLOSEOUT_OUTCOME
    assert closeout["selected_next_target"] == CONSUMED_TARGET

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
    assert review["synthesis_outcome_hint"] == SYNTHESIS_OUTCOME_HINT
    assert (
        build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review()
        == review
    )


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_preserves_chain() -> None:
    review = _json(DEFAULT_OUT)
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["accepted_review_findings_count"] == 8
    assert review["review_criteria_count"] == 8
    assert review["review_criteria_accepted_count"] == 8
    assert review["route_family_chain_count"] == 7
    assert review["current_candidate"] == CURRENT_CANDIDATE
    assert review["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert review["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert review["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert review["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert review["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert review["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert review["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert review["C_exchange_total_stress_energy_form"] == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    assert review["C_exchange_admissibility_condition"] == C_EXCHANGE_ADMISSIBILITY_CONDITION
    for key in [
        "closeout_result_review_prepared",
        "closeout_result_review_accepted",
        "closeout_accepted",
        "psi_A_interaction_family_closed",
        "interaction_exchange_rule_family_closed",
        "bounded_current_source_exchange_admissibility_family_closed",
        "current_source_exchange_total_conservation_route_preserved",
        "C_exchange_admissibility_only_preserved",
        "C_exchange_remains_admissibility_only",
        "master_action_ck_family_status_synthesis_authorized",
    ]:
        assert review[key] is True, key
    assert review["master_action_ck_family_status_synthesis_prepared"] is False
    assert review["ck_family_status_synthesis_prepared"] is False


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "direct_dynamical_law_interpretation_selected",
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
        "seam_closure_claim",
        "EM_QFT_closure",
        "QFT_GR_closure",
        "master_action_promotion",
    ]:
        assert review[key] is False, key
    for phrase in [
        "accepts only that the bounded psi-A U(1) interaction family is closed",
        "C_exchange remains admissibility-only",
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "working-form, noncanonical, non-promoted organizing surface",
        "full ToeFormal aggregate is kept as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["aggregate_lean_validation_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_review"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert review["aggregate_lean_validation_status_for_review"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_status_for_review"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_rotates_to_ck_family_status_synthesis() -> None:
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
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["closeout_result_review_prepared"] == "yes"
    assert consumed["closeout_result_review_accepted"] == "yes"
    assert consumed["C_exchange_remains_admissibility_only"] == "yes"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        assert NEXT_TARGET not in registry["completed_targets"]
        assert NEXT_TARGET not in registry["consumed_targets"]
        assert NEXT_TARGET not in registry["paused_lanes"]
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
        assert active_row["closeout_result_review_prepared"] == "yes"
        assert active_row["master_action_ck_family_status_synthesis_authorized"] == "yes"
        assert active_row["master_action_ck_family_status_synthesis_prepared"] == "no"
        assert active_row["ck_family_status_synthesis_prepared"] == "no"
        assert active_row["C_exchange_remains_admissibility_only"] == "yes"
        assert active_row["C_k_action_variation_executed"] == "no"
        assert active_row["em_qft_closure_claimed"] == "no"
        assert active_row["qft_gr_closure_claimed"] == "no"
        assert active_row["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
        synthesis_row = _workstream(registry, NEXT_TARGET)
        assert synthesis_row["status"] == "paused"
        assert synthesis_row["authorization_evidence"] == _rel(
            CK_FAMILY_STATUS_SYNTHESIS_LEAN_PACKET_PATH
        )
        assert synthesis_row["report"] == _rel(CK_FAMILY_STATUS_SYNTHESIS_OUT)
        assert synthesis_row["packet_result"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
        assert synthesis_row["outcome_id"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
        assert synthesis_row["result_token"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
        assert (
            synthesis_row["selected_next_target"]
            == CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
        )
        assert synthesis_row["selected_next_target_kind"] == (
            CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET_KIND
        )
        assert synthesis_row["master_action_ck_family_status_synthesis_prepared"] == "yes"
        assert synthesis_row["ck_family_status_synthesis_prepared"] == "yes"
        assert synthesis_row["ck_family_status_synthesis_result_review_prepared"] == "no"

        if CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET not in registry["completed_targets"]:
            active_row = _workstream(registry, CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET)
            assert active_row["status"] == "active"
            assert active_row["workstream_id"] == CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
            assert active_row["active_lane"] == CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
            assert active_row["authorized_next_strict_target"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
            )
            assert active_row["authorized_target"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
            )
            assert active_row["authorization_evidence"] == _rel(
                CK_FAMILY_STATUS_SYNTHESIS_LEAN_PACKET_PATH
            )
            assert active_row["report"] == _rel(CK_FAMILY_STATUS_SYNTHESIS_OUT)
            assert active_row["consumed_target"] == NEXT_TARGET
            assert active_row["packet_result"] == "PENDING"
            assert active_row["review_result"] == "PENDING"
            assert active_row["outcome_id"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
            assert active_row["selected_next_target"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
            )
            assert active_row["selected_next_target_kind"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET_KIND
            )
            assert active_row["master_action_ck_family_status_synthesis_prepared"] == "yes"
        else:
            review_row = _workstream(registry, CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET)
            assert review_row["status"] == "paused"
            assert review_row["authorization_evidence"] == _rel(
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH
            )
            assert review_row["report"] == _rel(
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUT
            )
            assert review_row["packet_result"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME
            )
            assert review_row["selected_next_target"] == (
                CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET
            )
            selector_row = _workstream(
                registry, CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET
            )
            if selector_row["status"] == "active":
                assert selector_row["workstream_id"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET
                )
                assert selector_row["active_lane"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET
                )
                assert selector_row["authorization_evidence"] == _rel(
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH
                )
                assert selector_row["report"] == _rel(
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUT
                )
                assert selector_row["consumed_target"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
                assert selector_row["packet_result"] == "PENDING"
                assert selector_row["review_result"] == "PENDING"
                assert selector_row["outcome_id"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME
                )
                assert selector_row["selected_next_target"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET
                )
                assert selector_row["selected_next_target_kind"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET_KIND
                )
            else:
                gap_target = "prepare_master_action_ck_family_gap_review_after_phi_A_and_psi_A"
                assert selector_row["status"] == "paused"
                assert selector_row["selected_next_target"] == gap_target
                assert selector_row["master_action_surface_selector_executed"] == "yes"
                assert selector_row["ck_family_gap_review_selected"] == "yes"
                gap_row = _workstream(registry, gap_target)
                if gap_row["status"] == "active":
                    assert gap_row["consumed_target"] == (
                        CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET
                    )
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
                    if active_gap_review["status"] == "active":
                        assert active_gap_review["consumed_target"] == gap_target
                        assert active_gap_review["gap_review_prepared"] == "yes"
                        assert active_gap_review["result_review_prepared"] == "no"
                    else:
                        post_review_selector = (
                            "select_next_master_action_surface_after_ck_family_gap_review"
                        )
                        assert active_gap_review["status"] == "paused"
                        assert active_gap_review["selected_next_target"] == (
                            post_review_selector
                        )
                        assert active_gap_review["result_review_prepared"] == "yes"
                        selector_row = _workstream(registry, post_review_selector)
                        if selector_row["status"] == "active":
                            assert selector_row["consumed_target"] == gap_review_target
                            assert selector_row["post_review_selector_executed"] == "no"
                            assert selector_row[
                                "theorem_linkage_obligation_index_prepared"
                            ] == "no"
                        else:
                            selector_review_target = (
                                "review_master_action_surface_selection_after_ck_family_gap_review_result"
                            )
                            assert selector_row["status"] == "paused"
                            assert selector_row["selected_next_target"] == (
                                selector_review_target
                            )
                            assert selector_row[
                                "selected_follow_on_target_after_review"
                            ] == "prepare_ck_family_theorem_linkage_obligation_index"
                            selector_review = _workstream(
                                registry, selector_review_target
                            )
                            assert selector_review["status"] == "active"
                            assert selector_review["consumed_target"] == (
                                post_review_selector
                            )
                            assert selector_review[
                                "selected_follow_on_target_after_review"
                            ] == "prepare_ck_family_theorem_linkage_obligation_index"
                            assert selector_review[
                                "theorem_linkage_obligation_index_selected"
                            ] == "yes"
                            assert selector_review[
                                "theorem_linkage_obligation_index_prepared"
                            ] == "no"


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_mirrors() -> None:
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
        "ToeNativePsiAU1InteractionExchangeRuleFamilyCloseoutResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET,
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_NONCLAIM_BOUNDARY_v0",
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_OBJECT,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        SYNTHESIS_OUTCOME_HINT,
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no C_k action variation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_result_review_gate.py"
    )
