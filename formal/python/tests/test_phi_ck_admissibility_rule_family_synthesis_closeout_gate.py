from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_ck_admissibility_rule_family_synthesis_closeout_report import (
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_RULE_CLASSIFICATION,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RECOMMENDED_AFTER_CLOSEOUT_CANDIDATE_FAMILY,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_FAMILY_EPISTEMIC_STATUS,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_PLAIN_MEANING,
    SYNTHESIS_RESULT_REVIEW_OUTCOME,
    SYNTHESIS_RESULT_REVIEW_PATH,
    SYNTHESIS_REVIEW_RESULT,
    build_phi_ck_admissibility_rule_family_synthesis_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_ck_admissibility_rule_family_synthesis_closeout_report.py"
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
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_phi_ck_admissibility_rule_family_synthesis_closeout_files_exist() -> None:
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


def test_phi_ck_admissibility_rule_family_synthesis_closeout_accepts_review() -> None:
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
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_phi_ck_admissibility_rule_family_synthesis_closeout() == closeout


def test_phi_ck_admissibility_rule_family_synthesis_closeout_preserves_family() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["family_classification"] == FIRST_SYNTHESIZED_FAMILY_CLASSIFICATION
    assert closeout["family_epistemic_status"] == RULE_FAMILY_EPISTEMIC_STATUS
    assert closeout["phi_ck_admissibility_rule_family_count"] == 2
    assert closeout["concrete_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
    ]
    assert closeout["source_rule_classification"] == SOURCE_RULE_CLASSIFICATION
    assert closeout["source_rule_epistemic_status"] == "admissibility-only"
    assert closeout["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert closeout["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert closeout["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert closeout["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["source_rule_plain_meaning"] == SOURCE_RULE_PLAIN_MEANING
    assert closeout["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert closeout["bridge_rule_epistemic_status"] == BRIDGE_RULE_EPISTEMIC_STATUS
    assert closeout["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert closeout["bridge_candidate_type"] == BRIDGE_CANDIDATE_TYPE
    assert closeout["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert closeout["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert closeout["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["bridge_route_field_equation_match"] == (
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert closeout["bridge_route_stress_energy_match"] == (
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert closeout["bridge_route_source_residual_match"] == (
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )


def test_phi_ck_admissibility_rule_family_synthesis_closeout_blocks_claims() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 9
    assert closeout["closeout_criteria_accepted_count"] == 9
    for key in [
        "closeout_prepared",
        "closeout_accepted",
        "first_synthesized_phi_relevant_ck_admissibility_rule_family_closed",
        "source_and_bridge_admissibility_rule_family_closed",
        "source_admissibility_rule_closed_in_family",
        "bridge_admissibility_rule_closed_in_family",
        "c_k_source_permission_role_closed",
        "c_k_bridge_permission_role_closed",
        "both_rules_admissibility_only",
        "both_rules_rule_candidates",
        "both_rules_not_action_terms",
        "both_rules_not_dynamical_laws",
        "neither_rule_derives_phi",
        "neither_rule_derives_v_phi",
        "selector_target_authorized",
    ]:
        assert closeout[key] is True, key
    assert closeout["selector_target_prepared"] is False
    assert closeout["recommended_next_ck_constraint_family"] == (
        RECOMMENDED_AFTER_CLOSEOUT_CANDIDATE_FAMILY
    )
    assert closeout["transport_chain_form"] == (
        "ACTION -> VARIATION -> BRIDGE -> OPERATOR -> TRANSPORT -> "
        "RESIDUAL_LAW -> REGIME_LIMIT"
    )
    for key in [
        "transport_consistency_family_selected",
        "another_phi_derivation_selected",
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "dynamical_law_claimed",
        "candidate_recorded_as_new_physical_law",
        "candidate_recorded_as_action_term",
        "ck_action_embedding_claimed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_executed",
        "phi_variation_executed",
        "bridge_admissibility_proved",
        "route_alignment_verified",
        "source_admissibility_proved",
        "source_conservation_proved",
        "native_phi_derivation_claimed",
        "phi_generated_by_ck_claimed",
        "phi_generation_theorem_claimed",
        "v_phi_derivation_claimed",
        "derived_v_phi_claimed",
        "potential_derived",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "native_generation_theorem_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert closeout[key] is False, key
    for phrase in [
        "not action terms",
        "not dynamical laws",
        "not native phi derivation",
        "not V(phi) derivation",
        "not QFT-GR closure",
        "not master-action promotion",
        "does not execute C_k variation",
        "does not select transport consistency",
    ]:
        assert phrase in closeout["non_claim_boundary"]


def test_phi_ck_admissibility_rule_family_synthesis_closeout_validation_policy() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert closeout["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert closeout["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert closeout["full_toeformal_aggregate_passed"] is False
    assert closeout["full_toeformal_aggregate_failed"] is False
    assert closeout["full_toeformal_aggregate_timed_out"] is False


def test_phi_ck_admissibility_rule_family_synthesis_closeout_rotates_to_selector() -> None:
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
        "PhiCKAdmissibilityRuleFamilySynthesisCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_CLOSEOUT_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["closeout_accepted"] == "yes"
    assert consumed["first_synthesized_phi_relevant_ck_admissibility_rule_family_closed"] == "yes"
    assert consumed["source_and_bridge_admissibility_rule_family_closed"] == "yes"
    assert consumed["selector_target_authorized"] == "yes"
    assert consumed["selector_target_prepared"] == "no"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert consumed["full_toeformal_aggregate_timed_out"] == "no"
    assert consumed["transport_consistency_family_selected"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["selector_target_authorized"] == "yes"
    assert active_row["selector_target_prepared"] == "no"
    assert active_row["recommended_next_ck_constraint_family"] == (
        "transport_consistency_ck_constraint_family"
    )
    assert active_row["transport_consistency_family_selected"] == "no"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_ck_admissibility_rule_family_synthesis_closeout_mirrors() -> None:
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        "PhiCKAdmissibilityRuleFamilySynthesisCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: select_next_ck_constraint_family_after_phi_source_and_bridge_admissibility",
        SOURCE_CANDIDATE_CONSTRAINT_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "first synthesized phi-relevant C_k admissibility-rule family",
        "source admissibility",
        "bridge admissibility",
        "transport_consistency_ck_constraint_family",
        "not action terms",
        "not dynamical laws",
        "not native phi derivation",
        "not V(phi) derivation",
        "not QFT-GR closure",
        "not master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_phi_ck_admissibility_rule_family_synthesis_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_ck_admissibility_rule_family_synthesis_closeout_gate.py"
    )
