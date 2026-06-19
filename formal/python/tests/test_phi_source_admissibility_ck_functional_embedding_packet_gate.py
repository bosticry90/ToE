from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_source_admissibility_ck_constraint_candidate_packet_result_review_report import (
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
)
from formal.python.tools.phi_source_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRECT_DIVERGENCE_INSERTION_FORM,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    QUADRATIC_PENALTY_ACTION_FORM,
    QUADRATIC_PENALTY_ROUTE_ID,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RESIDUAL_IDENTITY_FORM,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    WEAK_INTEGRATED_FORM,
    build_phi_source_admissibility_ck_functional_embedding_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_admissibility_ck_functional_embedding_packet_report.py"
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


def test_phi_source_admissibility_ck_functional_embedding_files_exist() -> None:
    for path in [
        CANDIDATE_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_source_admissibility_ck_functional_embedding_records_routes() -> None:
    review = _json(CANDIDATE_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == CANDIDATE_REVIEW_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert packet["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert packet["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert packet["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert packet["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert packet["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert packet["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert packet["on_shell_implication_form"] == ON_SHELL_IMPLICATION_FORM
    assert packet["admissibility_constraint_form"] == ADMISSIBILITY_CONSTRAINT_FORM
    assert packet["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert packet["direct_divergence_insertion_form"] == DIRECT_DIVERGENCE_INSERTION_FORM
    assert packet["weak_integrated_form"] == WEAK_INTEGRATED_FORM
    assert packet["quadratic_penalty_action_form"] == QUADRATIC_PENALTY_ACTION_FORM
    assert build_phi_source_admissibility_ck_functional_embedding_packet() == packet


def test_phi_source_admissibility_ck_functional_embedding_route_statuses() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["embedding_route_count"] == 3
    routes = {row["route_id"]: row for row in packet["embedding_routes"]}
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["status"] == (
        "selected_non_dynamical_admissibility_rule"
    )
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["selected_for_current_packet"] is True
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["action_term_selected"] is False
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["status"] == (
        "blocked_by_multiplier_domain_boundary_and_higher_derivative_scope"
    )
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["selected_for_current_packet"] is False
    assert "higher-derivative scope not controlled" in (
        routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["blocking_reasons"]
    )
    assert routes[QUADRATIC_PENALTY_ROUTE_ID]["status"] == "recorded_not_licensed"
    assert routes[QUADRATIC_PENALTY_ROUTE_ID]["selected_for_current_packet"] is False
    assert packet["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert packet["review_row_count"] == 10
    assert packet["review_row_accepted_count"] == 10
    assert {row["row_id"] for row in packet["review_rows"]} == {
        "consumes_expected_functional_embedding_target",
        "conservation_residual_candidate_carried_forward",
        "route_identity_carried_forward",
        "three_embedding_routes_recorded",
        "admissibility_only_route_selected",
        "lagrange_multiplier_route_blocked",
        "quadratic_penalty_route_not_licensed",
        "no_action_variation_executed",
        "no_new_proof_or_generation_claim",
        "no_closure_or_promotion_claim",
    }


def test_phi_source_admissibility_ck_functional_embedding_blocks_action_claims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["functional_embedding_packet_prepared"] is True
    assert packet["functional_embedding_options_recorded"] is True
    assert packet["admissibility_only_route_selected"] is True
    assert packet["constraint_as_admissibility_rule_selected"] is True
    assert packet["lagrange_multiplier_route_recorded"] is True
    assert packet["lagrange_multiplier_route_blocked"] is True
    assert packet["quadratic_penalty_route_recorded"] is True
    for key in [
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "weak_integrated_form_boundary_controlled",
        "quadratic_penalty_route_licensed",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "lambda_nu_domain_selected",
        "lambda_nu_variational_role_selected",
        "higher_derivative_scope_resolved",
        "boundary_terms_controlled",
        "regularity_domain_of_c_source_defined_for_action_embedding",
        "covariance_of_lambda_c_source_established",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "ck_functional_formula_fully_defined",
        "ck_functional_formula_selected",
        "candidate_action_insertion_executed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "quadratic_penalty_variation_executed",
        "ck_family_claimed_as_physical_law",
        "phi_generated_by_ck_claimed",
        "phi_generation_theorem_claimed",
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
        "standard_model_derivation_claimed",
        "native_generation_theorem_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    assert "selects the admissibility-only route" in packet["non_claim_boundary"]
    assert "does not embed it in S_C" in packet["non_claim_boundary"]
    assert "does not select lambda_nu or its domain" in packet["non_claim_boundary"]
    assert "does not control boundary terms" in packet["non_claim_boundary"]
    assert "does not resolve higher-derivative scope" in packet["non_claim_boundary"]
    assert "no source admissibility or conservation" in packet["non_claim_boundary"]
    assert "no QFT-GR closure" in packet["non_claim_boundary"]


def test_phi_source_admissibility_ck_functional_embedding_validation_policy() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_source_admissibility_ck_functional_embedding_rotates_to_review_target() -> None:
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
        "PhiSourceAdmissibilityCKFunctionalEmbeddingPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed["quadratic_penalty_route_licensed"] == "no"
    assert consumed["ck_variation_executed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["review_prepared"] == "no"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["lambda_nu_domain_selected"] == "no"
    assert active_row["higher_derivative_scope_resolved"] == "no"
    assert active_row["boundary_terms_controlled"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_source_admissibility_ck_functional_embedding_mirrors() -> None:
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
        PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "PhiSourceAdmissibilityCKFunctionalEmbeddingPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_phi_source_admissibility_ck_functional_embedding_packet_result",
        ADMISSIBILITY_ONLY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ROUTE_ID,
        QUADRATIC_PENALTY_ROUTE_ID,
        ADMISSIBILITY_CONSTRAINT_FORM,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        WEAK_INTEGRATED_FORM,
        QUADRATIC_PENALTY_ACTION_FORM,
        "selects the admissibility-only route",
        "does not embed it in S_C",
        "does not select lambda_nu or its domain",
        "does not resolve higher-derivative scope",
        "does not select or define a fully concrete C_k functional",
        "C_k remains inactive and undefined",
        "V(phi) remains smooth bounded-below but not derived",
        "C_k does not yet generate phi",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_phi_source_admissibility_ck_functional_embedding_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_admissibility_ck_functional_embedding_packet_gate.py"
    )
