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
from formal.python.tools.toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_report import (
    ARTIFACT_ID,
    C_EXCHANGE_ADMISSIBILITY_CONDITION,
    C_EXCHANGE_CANDIDATE_SCOPE,
    C_EXCHANGE_CONSTRAINT_FORM,
    C_EXCHANGE_CONSTRAINT_ID,
    C_EXCHANGE_PLAIN_MEANING,
    C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_CANDIDATE,
    CURRENT_CONSERVATION_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EXCHANGE_TERM_CANCELLATION,
    FAMILY_CLASSIFICATION,
    FAMILY_EPISTEMIC_STATUS,
    FAMILY_SCOPE,
    FOLLOW_ON_DECISION_TARGET_HINT,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_SECTOR_EXCHANGE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_SECTOR_EXCHANGE_IDENTITY,
    NARROW_FOLLOW_ON_SYNTHESIS_TARGET_HINT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_CLASSIFICATION,
    RULE_EPISTEMIC_STATUS,
    RULE_FAMILY_CLASSIFICATION,
    RULE_FAMILY_EPISTEMIC_STATUS,
    RULE_FAMILY_ID,
    SCHEMA_ID,
    SOURCE_CURRENT,
    SOURCED_GAUGE_ROUTE,
    SYNTHESIS_RESULT_REVIEW_OUTCOME,
    SYNTHESIS_RESULT_REVIEW_PATH,
    SYNTHESIS_REVIEW_RESULT,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_OBJECT,
    build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout,
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
    NEXT_TARGET_KIND as CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET_KIND,
    OUTCOME_ID as CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_report.py"
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


def test_psi_a_u1_interaction_exchange_rule_family_closeout_files_exist() -> None:
    for path in [
        SYNTHESIS_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_interaction_exchange_rule_family_closeout_accepts_review() -> None:
    review = _json(SYNTHESIS_RESULT_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == SYNTHESIS_RESULT_REVIEW_OUTCOME
    assert review["review_result"] == SYNTHESIS_REVIEW_RESULT
    assert review["selected_next_target"] == CONSUMED_TARGET

    assert closeout["artifact_id"] == ARTIFACT_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_result"] == CLOSEOUT_RESULT
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout() == (
        closeout
    )


def test_psi_a_u1_interaction_exchange_rule_family_closeout_preserves_chain() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["family_classification"] == FAMILY_CLASSIFICATION
    assert closeout["family_scope"] == FAMILY_SCOPE
    assert closeout["family_epistemic_status"] == FAMILY_EPISTEMIC_STATUS
    assert closeout["rule_family_id"] == RULE_FAMILY_ID
    assert closeout["rule_family_classification"] == RULE_FAMILY_CLASSIFICATION
    assert closeout["rule_family_epistemic_status"] == RULE_FAMILY_EPISTEMIC_STATUS
    assert closeout["route_family_chain_count"] == 7
    assert closeout["closed_route_roles"] == [
        "current candidate",
        "current conservation",
        "sourced gauge route",
        "gauge-sector exchange",
        "matter-sector exchange",
        "total stress-energy conservation",
        "interaction exchange-balance admissibility rule",
    ]
    assert closeout["current_candidate"] == CURRENT_CANDIDATE
    assert closeout["source_current"] == SOURCE_CURRENT
    assert closeout["current_conservation_result"] == CURRENT_CONSERVATION_RESULT
    assert closeout["sourced_gauge_route"] == SOURCED_GAUGE_ROUTE
    assert closeout["gauge_sector_exchange_identity"] == GAUGE_SECTOR_EXCHANGE_IDENTITY
    assert closeout["matter_sector_exchange_identity"] == MATTER_SECTOR_EXCHANGE_IDENTITY
    assert closeout["exchange_term_cancellation"] == EXCHANGE_TERM_CANCELLATION
    assert closeout["total_stress_energy_object"] == TOTAL_STRESS_ENERGY_OBJECT
    assert closeout["total_stress_energy_conservation_identity"] == (
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert closeout["C_exchange_constraint_id"] == C_EXCHANGE_CONSTRAINT_ID
    assert closeout["C_exchange_constraint_form"] == C_EXCHANGE_CONSTRAINT_FORM
    assert closeout["C_exchange_total_stress_energy_form"] == C_EXCHANGE_TOTAL_STRESS_ENERGY_FORM
    assert closeout["C_exchange_admissibility_condition"] == C_EXCHANGE_ADMISSIBILITY_CONDITION
    assert closeout["C_exchange_candidate_scope"] == C_EXCHANGE_CANDIDATE_SCOPE
    assert closeout["C_exchange_plain_meaning"] == C_EXCHANGE_PLAIN_MEANING
    assert closeout["C_exchange_rule_classification"] == RULE_CLASSIFICATION
    assert closeout["C_exchange_rule_epistemic_status"] == RULE_EPISTEMIC_STATUS


def test_psi_a_u1_interaction_exchange_rule_family_closeout_blocks_claims() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 10
    assert closeout["closeout_criteria_accepted_count"] == 10
    for key in [
        "closeout_prepared",
        "closeout_accepted",
        "review_accepted",
        "synthesis_result_review_accepted",
        "interaction_exchange_rule_family_closed",
        "bounded_current_source_exchange_admissibility_family_closed",
        "psi_A_current_route_closed",
        "current_conservation_route_closed",
        "sourced_maxwell_route_closed_as_bounded_context",
        "gauge_sector_exchange_route_closed",
        "matter_sector_exchange_route_closed",
        "total_stress_energy_conservation_route_closed",
        "C_exchange_admissibility_rule_closed",
        "C_exchange_rule_closed_as_interaction_exchange_balance_rule",
        "C_exchange_remains_admissibility_only",
        "master_action_remains_working_form_noncanonical",
        "claim_ladder_below_seam_closure",
        "closeout_result_review_authorized",
    ]:
        assert closeout[key] is True, key
    assert closeout["follow_on_decision_target_hint"] == FOLLOW_ON_DECISION_TARGET_HINT
    assert closeout["narrow_follow_on_synthesis_target_hint"] == (
        NARROW_FOLLOW_ON_SYNTHESIS_TARGET_HINT
    )
    for key in [
        "functional_action_embedding_claimed",
        "C_exchange_functional_embedding_claimed",
        "C_k_action_embedding_claimed",
        "C_k_action_embedding_selected",
        "C_k_action_variation_executed",
        "C_k_action_variation_authorized",
        "multiplier_route_selected",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "candidate_varied",
        "direct_dynamical_law_claimed",
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
        "post_closeout_decision_executed",
        "master_action_surface_selected_after_closeout",
        "ck_family_status_synthesis_prepared",
    ]:
        assert closeout[key] is False, key
    for phrase in [
        "bounded psi-A U(1) interaction",
        "J^mu = q psibar gamma^mu psi",
        "nabla_mu J^mu = 0",
        "nabla_mu F^{mu nu} = J^nu",
        "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha",
        "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha",
        "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}",
        "nabla_mu T_total^{mu nu} = 0",
        "C_exchange^{Apsi,nu}[g,A,psi] := nabla_mu T_total^{mu nu}",
        "C_exchange^{Apsi,nu} = 0",
        "no C_k action embedding",
        "no C_k action variation",
        "no multiplier route",
        "no penalty route",
        "no direct dynamical-law claim",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no anomaly analysis",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical, non-promoted organizing surface",
    ]:
        assert phrase in closeout["non_claim_boundary"], phrase


def test_psi_a_u1_interaction_exchange_rule_family_closeout_validation_policy() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert closeout["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert closeout["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert closeout["full_toeformal_aggregate_passed"] is False
    assert closeout["full_toeformal_aggregate_failed"] is False
    assert closeout["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_interaction_exchange_rule_family_closeout_rotates_to_result_review() -> None:
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
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == str(DEFAULT_OUT.relative_to(REPO_ROOT)).replace("\\", "/")
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["outcome_id"] == OUTCOME_ID
    assert consumed["result_token"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["interaction_exchange_rule_family_closeout_prepared"] == "yes"
    assert consumed["interaction_exchange_rule_family_closed"] == "yes"
    assert consumed["bounded_current_source_exchange_admissibility_family_closed"] == "yes"
    assert consumed["C_exchange_admissibility_rule_closed"] == "yes"
    assert consumed["C_exchange_rule_family_closed"] == "yes"
    assert consumed["C_exchange_remains_admissibility_only"] == "yes"
    assert consumed["C_k_action_variation_executed"] == "no"
    assert consumed["multiplier_route_selected"] == "no"
    assert consumed["penalty_route_selected"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    result_review_row = _workstream(registry, NEXT_TARGET)
    assert result_review_row["workstream_id"] == NEXT_TARGET
    assert result_review_row["interaction_exchange_rule_family_closeout_prepared"] == "yes"
    assert result_review_row["interaction_exchange_rule_family_closed"] == "yes"
    assert result_review_row["bounded_current_source_exchange_admissibility_family_closed"] == "yes"
    assert result_review_row["C_exchange_admissibility_rule_closed"] == "yes"
    assert result_review_row["C_exchange_rule_family_closed"] == "yes"
    assert result_review_row["C_exchange_remains_admissibility_only"] == "yes"
    assert result_review_row["C_k_action_variation_executed"] == "no"
    assert result_review_row["multiplier_route_selected"] == "no"
    assert result_review_row["penalty_route_selected"] == "no"
    assert result_review_row["em_qft_closure_claimed"] == "no"
    assert result_review_row["qft_gr_closure_claimed"] == "no"
    assert result_review_row["master_action_promoted"] == "no"

    if is_current:
        assert NEXT_TARGET not in registry["completed_targets"]
        assert NEXT_TARGET not in registry["consumed_targets"]
        assert NEXT_TARGET not in registry["paused_lanes"]
        assert result_review_row["status"] == "active"
        assert result_review_row["active_lane"] == NEXT_TARGET
        assert result_review_row["authorized_next_strict_target"] == NEXT_TARGET
        assert result_review_row["authorized_target"] == NEXT_TARGET
        assert result_review_row["authorization_evidence"] == evidence
        assert result_review_row["report"] == str(DEFAULT_OUT.relative_to(REPO_ROOT)).replace("\\", "/")
        assert result_review_row["consumed_target"] == CONSUMED_TARGET
        assert result_review_row["packet_result"] == "PENDING"
        assert result_review_row["review_result"] == "PENDING"
        assert result_review_row["result_review_prepared"] == "no"
        assert result_review_row["closeout_result"] == OUTCOME_ID
        assert result_review_row["outcome_id"] == OUTCOME_ID
        assert result_review_row["result_token"] == OUTCOME_ID
        assert result_review_row["selected_next_target"] == NEXT_TARGET
        assert result_review_row["selected_next_target_kind"] == NEXT_TARGET_KIND
        assert result_review_row["follow_on_decision_executed"] == "no"
        assert result_review_row["master_action_surface_selected_after_closeout"] == "no"
        assert result_review_row["ck_family_status_synthesis_prepared"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
        assert result_review_row["status"] == "paused"
        assert result_review_row["authorization_evidence"] == str(
            CLOSEOUT_REVIEW_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
        ).replace("\\", "/")
        assert result_review_row["report"] == str(CLOSEOUT_REVIEW_OUT.relative_to(REPO_ROOT)).replace(
            "\\", "/"
        )
        assert result_review_row["packet_result"] == CLOSEOUT_REVIEW_OUTCOME
        assert result_review_row["review_result"] == CLOSEOUT_REVIEW_OUTCOME
        assert result_review_row["outcome_id"] == CLOSEOUT_REVIEW_OUTCOME
        assert result_review_row["result_token"] == CLOSEOUT_REVIEW_OUTCOME
        assert result_review_row["selected_next_target"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
        assert result_review_row["selected_next_target_kind"] == (
            CK_FAMILY_STATUS_SYNTHESIS_TARGET_KIND
        )
        assert result_review_row["closeout_result_review_prepared"] == "yes"
        assert result_review_row["closeout_result_review_accepted"] == "yes"

        synthesis_row = _workstream(registry, CK_FAMILY_STATUS_SYNTHESIS_TARGET)
        if synthesis_row["status"] == "active":
            assert synthesis_row["workstream_id"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
            assert synthesis_row["active_lane"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
            assert (
                synthesis_row["authorized_next_strict_target"]
                == CK_FAMILY_STATUS_SYNTHESIS_TARGET
            )
            assert synthesis_row["authorized_target"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
            assert synthesis_row["authorization_evidence"] == str(
                CLOSEOUT_REVIEW_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
            ).replace("\\", "/")
            assert synthesis_row["report"] == str(
                CLOSEOUT_REVIEW_OUT.relative_to(REPO_ROOT)
            ).replace("\\", "/")
            assert synthesis_row["consumed_target"] == NEXT_TARGET
            assert synthesis_row["packet_result"] == "PENDING"
            assert synthesis_row["review_result"] == "PENDING"
            assert synthesis_row["outcome_id"] == CLOSEOUT_REVIEW_OUTCOME
            assert synthesis_row["selected_next_target"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
            assert (
                synthesis_row["selected_next_target_kind"]
                == CK_FAMILY_STATUS_SYNTHESIS_TARGET_KIND
            )
            assert synthesis_row["master_action_ck_family_status_synthesis_prepared"] == "no"
        else:
            assert synthesis_row["status"] == "paused"
            assert synthesis_row["authorization_evidence"] == str(
                CK_FAMILY_STATUS_SYNTHESIS_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
            ).replace("\\", "/")
            assert synthesis_row["report"] == str(
                CK_FAMILY_STATUS_SYNTHESIS_OUT.relative_to(REPO_ROOT)
            ).replace("\\", "/")
            assert synthesis_row["packet_result"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
            assert synthesis_row["outcome_id"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
            assert synthesis_row["result_token"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
            assert synthesis_row["selected_next_target"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
            )
            assert synthesis_row["selected_next_target_kind"] == (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET_KIND
            )
            assert synthesis_row["master_action_ck_family_status_synthesis_prepared"] == "yes"

            if (
                CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                not in registry["completed_targets"]
            ):
                active_row = _workstream(
                    registry, CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
                assert active_row["status"] == "active"
                assert active_row["workstream_id"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
                assert active_row["active_lane"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
                assert active_row["authorization_evidence"] == str(
                    CK_FAMILY_STATUS_SYNTHESIS_LEAN_PACKET_PATH.relative_to(REPO_ROOT)
                ).replace("\\", "/")
                assert active_row["report"] == str(
                    CK_FAMILY_STATUS_SYNTHESIS_OUT.relative_to(REPO_ROOT)
                ).replace("\\", "/")
                assert active_row["consumed_target"] == CK_FAMILY_STATUS_SYNTHESIS_TARGET
                assert active_row["packet_result"] == "PENDING"
                assert active_row["review_result"] == "PENDING"
                assert active_row["outcome_id"] == CK_FAMILY_STATUS_SYNTHESIS_OUTCOME
                assert active_row["selected_next_target"] == (
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
            else:
                review_row = _workstream(
                    registry, CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET
                )
                assert review_row["status"] == "paused"
                assert review_row["authorization_evidence"] == str(
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH.relative_to(
                        REPO_ROOT
                    )
                ).replace("\\", "/")
                assert review_row["report"] == str(
                    CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUT.relative_to(REPO_ROOT)
                ).replace("\\", "/")
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
                    assert selector_row["authorization_evidence"] == str(
                        CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_LEAN_PACKET_PATH.relative_to(
                            REPO_ROOT
                        )
                    ).replace("\\", "/")
                    assert selector_row["report"] == str(
                        CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUT.relative_to(REPO_ROOT)
                    ).replace("\\", "/")
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
                    gap_target = (
                        "prepare_master_action_ck_family_gap_review_after_phi_A_and_psi_A"
                    )
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
                                if selector_review["status"] == "active":
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
                                else:
                                    theorem_index_target = (
                                        "prepare_ck_family_theorem_linkage_obligation_index"
                                    )
                                    assert selector_review["status"] == "paused"
                                    assert selector_review["selected_next_target"] == (
                                        theorem_index_target
                                    )
                                    assert selector_review[
                                        "selector_result_review_accepted"
                                    ] == "yes"
                                    active_index = _workstream(
                                        registry, theorem_index_target
                                    )
                                    assert active_index["status"] == "active"
                                    assert active_index["consumed_target"] == (
                                        selector_review_target
                                    )
                                    assert active_index[
                                        "theorem_linkage_obligation_index_selected"
                                    ] == "yes"
                                    assert active_index[
                                        "theorem_linkage_obligation_index_prepared"
                                    ] == "no"
                                    assert active_index["obligation_rows_discharged"] == "no"
                                    assert active_index["master_action_promoted"] == "no"


def test_psi_a_u1_interaction_exchange_rule_family_closeout_mirrors() -> None:
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
        CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1InteractionExchangeRuleFamilyCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_TARGET,
        CK_FAMILY_STATUS_SYNTHESIS_SURFACE_SELECTOR_TARGET,
        CLOSEOUT_REVIEW_OUTCOME,
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_OUTCOME_v0",
        "TOE_NATIVE_PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_OUTCOME_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "PSI_A_U1_INTERACTION_EXCHANGE_RULE_FAMILY_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_NONCLAIM_BOUNDARY_v0",
        CURRENT_CANDIDATE,
        CURRENT_CONSERVATION_RESULT,
        SOURCE_CURRENT,
        SOURCED_GAUGE_ROUTE,
        GAUGE_SECTOR_EXCHANGE_IDENTITY,
        MATTER_SECTOR_EXCHANGE_IDENTITY,
        TOTAL_STRESS_ENERGY_OBJECT,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_CONSTRAINT_FORM,
        C_EXCHANGE_ADMISSIBILITY_CONDITION,
        FOLLOW_ON_DECISION_TARGET_HINT,
        NARROW_FOLLOW_ON_SYNTHESIS_TARGET_HINT,
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no C_k action variation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_psi_a_u1_interaction_exchange_rule_family_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_interaction_exchange_rule_family_closeout_gate.py"
    )
