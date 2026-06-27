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
from formal.python.tools.master_action_surface_selection_after_ck_family_status_synthesis_report import (
    DEFAULT_OUT as SELECTOR_OUT,
    NEXT_TARGET as SELECTOR_NEXT_TARGET,
    OUTCOME_ID as SELECTOR_OUTCOME,
)
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_report import (
    ALTERNATE_POST_REVIEW_BRANCH,
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
    GAP_REVIEW_INSPECTION_QUESTIONS,
    LEAN_PACKET_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_POST_REVIEW_BRANCH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_MASTER_ACTION_SURFACE,
    SOURCED_GAUGE_ROUTE,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    build_master_action_ck_family_gap_review_after_phi_a_and_psi_a,
)
from formal.python.tools.master_action_ck_family_gap_review_after_phi_a_and_psi_a_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as RESULT_REVIEW_NEXT_TARGET,
    NEXT_TARGET_KIND as RESULT_REVIEW_NEXT_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RECOMMENDED_SELECTOR_CHOICE as RESULT_REVIEW_RECOMMENDED_SELECTOR_CHOICE,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_family_gap_review_after_phi_a_and_psi_a_report.py"
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


def test_master_action_ck_family_gap_review_files_exist() -> None:
    for path in [
        SELECTOR_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_master_action_ck_family_gap_review_accepts_selector() -> None:
    selector = _json(SELECTOR_OUT)
    payload = _json(DEFAULT_OUT)

    assert selector["outcome_id"] == SELECTOR_OUTCOME
    assert selector["selected_next_target"] == SELECTOR_NEXT_TARGET
    assert payload["artifact_id"] == ARTIFACT_ID
    assert payload["schema_id"] == SCHEMA_ID
    assert payload["packet_id"] == PACKET_ID
    assert payload["prepared"] is True
    assert payload["accepted"] is True
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["gap_review_result"] == OUTCOME_ID
    assert payload["packet_result"] == OUTCOME_ID
    assert payload["packet_classification"] == PACKET_CLASSIFICATION
    assert payload["consumed_target"] == CONSUMED_TARGET
    assert payload["selected_next_target"] == NEXT_TARGET
    assert payload["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert payload["selector_selected_surface"] == SELECTED_MASTER_ACTION_SURFACE
    assert build_master_action_ck_family_gap_review_after_phi_a_and_psi_a() == payload


def test_master_action_ck_family_gap_review_indexes_all_open_gaps() -> None:
    payload = _json(DEFAULT_OUT)
    rows = payload["gap_rows"]

    assert payload["gap_count"] == 8
    assert payload["open_gap_count"] == 8
    assert payload["closed_gap_count"] == 0
    assert [row["gap_id"] for row in rows] == [f"GAP-{index}" for index in range(1, 9)]
    assert [row["gap_label"] for row in rows] == [
        "theorem-linkage gap",
        "assumption gap",
        "functionalization gap",
        "variation gap",
        "physical-meaning gap",
        "interaction-generalization gap",
        "seam-closure gap",
        "empirical-discriminator gap",
    ]
    assert all(row["resolution_status"] == "open_indexed_only" for row in rows)
    assert payload["gap_review_inspection_questions"] == GAP_REVIEW_INSPECTION_QUESTIONS
    assert payload["gap_review_criteria_count"] == 7
    assert payload["gap_review_criteria_accepted_count"] == 7
    for key in [
        "admissibility_to_functionalization_gaps_indexed",
        "rule_family_gaps_indexed",
        "theorem_linkage_gap_indexed",
        "assumption_gap_indexed",
        "functionalization_gap_indexed",
        "variation_gap_indexed",
        "physical_meaning_gap_indexed",
        "interaction_generalization_gap_indexed",
        "seam_closure_gap_indexed",
        "empirical_discriminator_gap_indexed",
    ]:
        assert payload[key] is True, key
    assert payload["gap_review_closes_any_gap"] is False


def test_master_action_ck_family_gap_review_preserves_rule_context() -> None:
    payload = _json(DEFAULT_OUT)

    assert payload["C_source_classification"] == C_SOURCE_CLASSIFICATION
    assert payload["C_bridge_classification"] == C_BRIDGE_CLASSIFICATION
    assert payload["C_transport_classification"] == C_TRANSPORT_CLASSIFICATION
    assert payload["C_exchange_classification"] == C_EXCHANGE_CLASSIFICATION
    for token in [
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "GAP-1 through GAP-8",
    ]:
        assert token in payload["mathematical_statement"], token
    for key in [
        "all_C_k_families_admissibility_only",
        "all_summarized_rules_admissibility_only",
        "all_summarized_rules_not_action_embedded",
        "all_summarized_rules_not_varied",
        "all_summarized_rules_not_direct_dynamical_laws",
        "all_summarized_rules_not_empirical_claims",
    ]:
        assert payload[key] is True, key


def test_master_action_ck_family_gap_review_preserves_nonclaims_and_not_run() -> None:
    payload = _json(DEFAULT_OUT)
    for key in [
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_embedding_authorized",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "direct_dynamical_law_interpretation_selected",
        "functional_action_embedding_claimed",
        "functionalization_authorized",
        "full_maxwell_closure_claimed",
        "full_Maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_prediction_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
        "master_action_promotion",
        "theorem_linkage_completed",
        "assumption_discharge_completed",
        "variation_authorized",
        "seam_closure_authorized",
        "post_review_branch_selected",
        "result_review_prepared",
        "result_review_accepted",
    ]:
        assert payload[key] is False, key
    for phrase in [
        "C_k family gap review only",
        "admissibility-only rulebook",
        "The stronger structure is not authorized",
        "no C_k action embedding",
        "no C_k action variation",
        "no multiplier route",
        "no penalty route",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no empirical prediction or validation",
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


def test_master_action_ck_family_gap_review_rotates_to_result_review() -> None:
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
    assert consumed["gap_review_prepared"] == "yes"
    assert consumed["gap_review_accepted"] == "yes"
    assert consumed["gap_review_executed"] == "yes"
    assert str(consumed["gap_count"]) == "8"
    assert str(consumed["open_gap_count"]) == "8"
    assert str(consumed["closed_gap_count"]) == "0"
    assert consumed["result_review_prepared"] == "no"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["gr_qm_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if not is_current:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
        result_review = _workstream(registry, NEXT_TARGET)
        assert result_review["status"] == "paused"
        assert result_review["authorization_evidence"] == _rel(
            RESULT_REVIEW_LEAN_PACKET_PATH
        )
        assert result_review["report"] == _rel(RESULT_REVIEW_OUT)
        assert result_review["packet_result"] == RESULT_REVIEW_OUTCOME
        assert result_review["review_result"] == RESULT_REVIEW_OUTCOME
        assert result_review["outcome_id"] == RESULT_REVIEW_OUTCOME
        assert result_review["result_token"] == RESULT_REVIEW_OUTCOME
        assert result_review["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET
        assert result_review["selected_next_target_kind"] == (
            RESULT_REVIEW_NEXT_TARGET_KIND
        )
        assert result_review["result_review_prepared"] == "yes"
        assert result_review["result_review_accepted"] == "yes"
        assert result_review["no_gap_discharged"] == "yes"
        assert result_review["no_rule_promoted"] == "yes"
        assert result_review["no_C_k_functionalization_occurs"] == "yes"
        assert result_review["no_C_k_variation_occurs"] == "yes"
        assert result_review["no_seam_closure_occurs"] == "yes"
        assert result_review["master_action_promoted"] == "no"

        active = _workstream(registry, RESULT_REVIEW_NEXT_TARGET)
        if active["status"] == "active":
            assert active["workstream_id"] == RESULT_REVIEW_NEXT_TARGET
            assert active["active_lane"] == RESULT_REVIEW_NEXT_TARGET
            assert active["authorized_next_strict_target"] == RESULT_REVIEW_NEXT_TARGET
            assert active["authorized_target"] == RESULT_REVIEW_NEXT_TARGET
            assert active["authorization_evidence"] == _rel(RESULT_REVIEW_LEAN_PACKET_PATH)
            assert active["report"] == _rel(RESULT_REVIEW_OUT)
            assert active["consumed_target"] == NEXT_TARGET
            assert active["packet_result"] == "PENDING"
            assert active["review_result"] == "PENDING"
            assert active["outcome_id"] == RESULT_REVIEW_OUTCOME
            assert active["result_token"] == RESULT_REVIEW_OUTCOME
            assert active["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET
            assert active["selected_next_target_kind"] == RESULT_REVIEW_NEXT_TARGET_KIND
            assert active["recommended_selector_choice"] == (
                RESULT_REVIEW_RECOMMENDED_SELECTOR_CHOICE
            )
            assert active["post_review_selector_authorized"] == "yes"
            assert active["post_review_selector_executed"] == "no"
            assert active["theorem_linkage_obligation_index_prepared"] == "no"
            assert active["theorem_linkage_obligation_index_selected"] == "no"
            assert active["master_action_promoted"] == "no"
        else:
            selector_review_target = (
                "review_master_action_surface_selection_after_ck_family_gap_review_result"
            )
            assert active["status"] == "paused"
            assert active["selected_next_target"] == selector_review_target
            assert active["selected_follow_on_target_after_review"] == (
                "prepare_ck_family_theorem_linkage_obligation_index"
            )
            selector_review = _workstream(registry, selector_review_target)
            if selector_review["status"] == "active":
                assert selector_review["consumed_target"] == RESULT_REVIEW_NEXT_TARGET
                assert selector_review["selected_follow_on_target_after_review"] == (
                    "prepare_ck_family_theorem_linkage_obligation_index"
                )
                assert (
                    selector_review["theorem_linkage_obligation_index_selected"]
                    == "yes"
                )
                assert (
                    selector_review["theorem_linkage_obligation_index_prepared"]
                    == "no"
                )
                assert selector_review["master_action_promoted"] == "no"
            else:
                theorem_index_target = "prepare_ck_family_theorem_linkage_obligation_index"
                assert selector_review["status"] == "paused"
                assert selector_review["selected_next_target"] == theorem_index_target
                assert selector_review["selector_result_review_accepted"] == "yes"
                active_index = _workstream(registry, theorem_index_target)
                assert active_index["status"] == "active"
                assert active_index["consumed_target"] == selector_review_target
                assert active_index["theorem_linkage_obligation_index_selected"] == "yes"
                assert active_index["theorem_linkage_obligation_index_prepared"] == "no"
                assert active_index["obligation_rows_discharged"] == "no"
                assert active_index["master_action_promoted"] == "no"
        return

    assert NEXT_TARGET not in registry["completed_targets"]
    assert NEXT_TARGET not in registry["consumed_targets"]
    assert NEXT_TARGET not in registry["paused_lanes"]

    active = _workstream(registry, NEXT_TARGET)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["authorized_target"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["report"] == _rel(DEFAULT_OUT)
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["packet_result"] == "PENDING"
    assert active["review_result"] == "PENDING"
    assert active["outcome_id"] == OUTCOME_ID
    assert active["result_token"] == OUTCOME_ID
    assert active["selected_next_target"] == NEXT_TARGET
    assert active["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active["gap_review_prepared"] == "yes"
    assert active["gap_review_accepted"] == "yes"
    assert active["gap_review_executed"] == "yes"
    assert str(active["gap_count"]) == "8"
    assert str(active["open_gap_count"]) == "8"
    assert str(active["closed_gap_count"]) == "0"
    assert active["result_review_prepared"] == "no"
    assert active["result_review_accepted"] == "no"
    assert active["C_k_action_variation_executed"] == "no"
    assert active["em_qft_closure_claimed"] == "no"
    assert active["qft_gr_closure_claimed"] == "no"
    assert active["gr_qm_closure_claimed"] == "no"
    assert active["master_action_promoted"] == "no"


def test_master_action_ck_family_gap_review_mirrors() -> None:
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
        "MasterActionCKFamilyGapReviewAfterPhiAAndPsiA",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_NONCLAIM_BOUNDARY_v0",
        "GAP-1",
        "GAP-8",
        "theorem-linkage gap",
        "empirical-discriminator gap",
        RECOMMENDED_POST_REVIEW_BRANCH,
        ALTERNATE_POST_REVIEW_BRANCH,
        C_SOURCE_CLASSIFICATION,
        C_BRIDGE_CLASSIFICATION,
        C_TRANSPORT_CLASSIFICATION,
        C_EXCHANGE_CLASSIFICATION,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        "no C_k action embedding",
        "no C_k action variation",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_master_action_ck_family_gap_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_family_gap_review_after_phi_a_and_psi_a_gate.py"
    )
