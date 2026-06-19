from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_ck_constraint_family_selection_for_phi_route_report import (
    DEFAULT_OUT as CK_FAMILY_SELECTION_PATH,
    OUTCOME_ID as CK_FAMILY_SELECTION_OUTCOME,
)
from formal.python.tools.phi_source_admissibility_ck_constraint_candidate_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    CANDIDATE_ACTION_INSERTION_FORM,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
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
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    build_phi_source_admissibility_ck_constraint_candidate_packet,
)
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_packet_report import (
    DEFAULT_OUT as PHI_VARIATION_RETRY_PATH,
    OUTCOME_ID as PHI_VARIATION_RETRY_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_admissibility_ck_constraint_candidate_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
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
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_phi_source_admissibility_ck_candidate_files_exist() -> None:
    for path in [
        CK_FAMILY_SELECTION_PATH,
        PHI_VARIATION_RETRY_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_source_admissibility_ck_candidate_records_residual_shape() -> None:
    selector = _json(CK_FAMILY_SELECTION_PATH)
    retry = _json(PHI_VARIATION_RETRY_PATH)
    packet = _json(DEFAULT_OUT)
    assert selector["outcome_id"] == CK_FAMILY_SELECTION_OUTCOME
    assert retry["outcome_id"] == PHI_VARIATION_RETRY_OUTCOME
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
    assert packet["candidate_action_insertion_form"] == CANDIDATE_ACTION_INSERTION_FORM
    assert build_phi_source_admissibility_ck_constraint_candidate_packet() == packet


def test_phi_source_admissibility_ck_candidate_options_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_shape_count"] == 3
    assert packet["candidate_shape_selected_count"] == 1
    assert packet["candidate_shape_supporting_count"] == 1
    assert packet["candidate_shape_deferred_count"] == 1
    shapes = {row["candidate_type"]: row for row in packet["candidate_shapes"]}
    assert shapes["conservation_residual_constraint"]["selection_status"] == (
        "selected_as_first_candidate_shape"
    )
    assert shapes["on_shell_source_admissibility_residual"]["selection_status"] == (
        "recorded_as_supporting_route_identity"
    )
    assert shapes["route_bundle_admissibility_constraint"]["selection_status"] == (
        "deferred_as_non_variational_checklist"
    )
    assert packet["route_bundle_admissibility_form"] == ROUTE_BUNDLE_ADMISSIBILITY_FORM
    assert packet["review_row_count"] == 10
    assert packet["review_row_accepted_count"] == 10
    assert {row["row_id"] for row in packet["review_rows"]} == {
        "consumes_expected_candidate_packet_target",
        "selected_family_carried_forward",
        "selected_phi_policy_carried_forward",
        "phi_variation_route_reference_available",
        "conservation_residual_candidate_recorded",
        "on_shell_residual_identity_recorded",
        "route_bundle_deferred",
        "candidate_action_insertion_not_executed",
        "no_new_conservation_or_source_admissibility_proof",
        "no_closure_promotion_or_empirical_claim",
    }


def test_phi_source_admissibility_ck_candidate_blocks_variation_and_promotions() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_packet_prepared"] is True
    assert packet["candidate_constraint_shape_recorded"] is True
    assert packet["conservation_residual_candidate_selected"] is True
    assert packet["on_shell_source_admissibility_relation_recorded"] is True
    assert packet["route_bundle_admissibility_candidate_deferred"] is True
    assert packet["candidate_constraint_is_condition_not_physical_law"] is True
    for key in [
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
    assert "conservation residual" in packet["non_claim_boundary"]
    assert "does not select or define a fully concrete C_k functional" in (
        packet["non_claim_boundary"]
    )
    assert "no source admissibility or conservation" in packet["non_claim_boundary"]
    assert "no QFT-GR closure" in packet["non_claim_boundary"]


def test_phi_source_admissibility_ck_candidate_validation_policy() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_source_admissibility_ck_candidate_rotates_to_review_target() -> None:
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
        "PhiSourceAdmissibilityCKConstraintCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert consumed["candidate_constraint_shape_recorded"] == "yes"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["candidate_constraint_shape_recorded"] == "yes"
    assert active_row["review_prepared"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_source_admissibility_ck_candidate_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            CURRENT_AUTHORITY_AGGREGATE_PATH,
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
        "PhiSourceAdmissibilityCKConstraintCandidatePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_phi_source_admissibility_ck_constraint_candidate_packet_result",
        CANDIDATE_CONSTRAINT_ID,
        CANDIDATE_CONSTRAINT_FORM,
        CANDIDATE_CONSTRAINT_EQUATION,
        ON_SHELL_RESIDUAL_FORM,
        RESIDUAL_IDENTITY_FORM,
        "conservation residual",
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


def test_phi_source_admissibility_ck_candidate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_admissibility_ck_constraint_candidate_packet_gate.py"
    )
