from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_ck_admissibility_rule_family_synthesis_result_review_report import (
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
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
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
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLASSIFICATION,
    SOURCE_RULE_PLAIN_MEANING,
    SYNTHESIS_PACKET_OUTCOME,
    SYNTHESIS_PACKET_PATH,
    SYNTHESIS_PACKET_RESULT,
    build_phi_ck_admissibility_rule_family_synthesis_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_ck_admissibility_rule_family_synthesis_result_review_report.py"
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


def test_phi_ck_admissibility_rule_family_synthesis_result_review_files_exist() -> None:
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


def test_phi_ck_admissibility_rule_family_synthesis_result_review_accepts_packet() -> None:
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
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_phi_ck_admissibility_rule_family_synthesis_result_review() == review


def test_phi_ck_admissibility_rule_family_synthesis_result_review_preserves_rules() -> None:
    review = _json(DEFAULT_OUT)
    assert review["phi_ck_admissibility_rule_family_count"] == 2
    assert review["concrete_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
    ]
    assert review["source_rule_classification"] == SOURCE_RULE_CLASSIFICATION
    assert review["source_rule_epistemic_status"] == "admissibility-only"
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert review["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert review["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["source_rule_plain_meaning"] == SOURCE_RULE_PLAIN_MEANING
    assert review["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert review["bridge_rule_epistemic_status"] == BRIDGE_RULE_EPISTEMIC_STATUS
    assert review["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert review["bridge_candidate_type"] == BRIDGE_CANDIDATE_TYPE
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["bridge_route_field_equation_match"] == (
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert review["bridge_route_stress_energy_match"] == (
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert review["bridge_route_source_residual_match"] == (
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )


def test_phi_ck_admissibility_rule_family_synthesis_result_review_blocks_claims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 9
    assert review["review_criteria_accepted_count"] == 9
    for key in [
        "review_executed",
        "result_review_prepared",
        "result_review_accepted",
        "synthesis_packet_accepted",
        "source_rule_synthesis_accepted",
        "bridge_rule_synthesis_accepted",
        "source_and_bridge_rule_synthesis_accepted",
        "two_rule_family_review_accepted",
        "c_k_instantiated_as_admissibility_rules",
        "c_k_source_permission_role_accepted",
        "c_k_bridge_permission_role_accepted",
        "both_rules_admissibility_only",
        "both_rules_rule_candidates",
        "both_rules_not_action_terms",
        "both_rules_not_dynamical_laws",
        "neither_rule_derives_phi",
        "neither_rule_derives_v_phi",
        "synthesis_closeout_authorized",
    ]:
        assert review[key] is True, key
    assert review["synthesis_closeout_prepared"] is False
    for key in [
        "selector_after_closeout_authorized",
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
        assert review[key] is False, key
    assert "no action term" in review["non_claim_boundary"]
    assert "no C_k variation" in review["non_claim_boundary"]
    assert "no dynamical-law claim" in review["non_claim_boundary"]
    assert "no native phi derivation" in review["non_claim_boundary"]
    assert "no V(phi) derivation" in review["non_claim_boundary"]
    assert "no QFT-GR closure" in review["non_claim_boundary"]
    assert "no master-action promotion" in review["non_claim_boundary"]


def test_phi_ck_admissibility_rule_family_synthesis_result_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_phi_ck_admissibility_rule_family_synthesis_result_review_rotates_to_closeout() -> None:
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
        "PhiCKAdmissibilityRuleFamilySynthesisResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_CK_ADMISSIBILITY_RULE_FAMILY_SYNTHESIS_RESULT_REVIEW_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["source_rule_synthesis_accepted"] == "yes"
    assert consumed["bridge_rule_synthesis_accepted"] == "yes"
    assert consumed["synthesis_closeout_authorized"] == "yes"
    assert consumed["synthesis_closeout_prepared"] == "no"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert consumed["full_toeformal_aggregate_timed_out"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["synthesis_closeout_authorized"] == "yes"
    assert active_row["synthesis_closeout_prepared"] == "no"
    assert active_row["selector_after_closeout_authorized"] == "no"
    assert active_row["transport_consistency_family_selected"] == "no"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_ck_admissibility_rule_family_synthesis_result_review_mirrors() -> None:
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        "PhiCKAdmissibilityRuleFamilySynthesisResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_ck_admissibility_rule_family_synthesis_closeout",
        SOURCE_CANDIDATE_CONSTRAINT_FORM,
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source admissibility",
        "bridge admissibility",
        "no action term",
        "no C_k variation",
        "no dynamical-law claim",
        "no native phi derivation",
        "no V(phi) derivation",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_phi_ck_admissibility_rule_family_synthesis_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_ck_admissibility_rule_family_synthesis_result_review_gate.py"
    )
