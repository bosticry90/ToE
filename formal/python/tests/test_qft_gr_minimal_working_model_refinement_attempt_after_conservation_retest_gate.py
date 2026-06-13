from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_report import (
    ATTEMPT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    REFINEMENT_OBJECTIVE,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_conservation_retest_result_review_report import (
    DEFAULT_OUT as REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_PATH,
    OUTCOME_ID as REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_report.py"
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelRefinementAttemptAfterConservationRetest.lean"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
V01_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
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
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for item in payload["workstreams"]:
        if item["workstream_id"] == workstream_id:
            return item
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_minimal_working_model_refinement_attempt_after_retest_files_exist() -> None:
    assert REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_minimal_working_model_refinement_attempt_after_retest_consumes_review() -> None:
    attempt = _json(DEFAULT_OUT)
    review = _json(REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["accepted"] is True
    assert attempt["executed"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert attempt["attempt_classification"] == RESULT_CLASSIFICATION
    assert attempt["consumed_target"] == CONSUMED_TARGET
    assert (
        attempt[
            "consumes_qft_gr_minimal_working_model_refinement_after_retest_packet_result_review"
        ]
        == REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_ID
    )
    assert review["schema_id"] == REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_SCHEMA_ID
    assert review["review_id"] == REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_ID
    assert review["outcome_id"] == REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_OUTCOME
    assert (
        review["result_review_classification"]
        == REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_CLASSIFICATION
    )
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_refinement_attempt_after_retest_refines_authorized_dimensions_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["attempt_executed"] is True
    assert attempt["bounded_refinement_attempt_executed"] is True
    assert attempt["post_retest_refinement_attempt_executed"] is True
    assert attempt["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert attempt["selected_refinement_target"] == REFINEMENT_OBJECTIVE
    assert attempt["selected_refinement_target_count"] == 1
    assert attempt["refinement_scope"] == (
        "post_retest_weak_pairing_domain_regular_context_test_function_class_"
        "candidate_definition_scope_restriction_without_source_admissibility"
    )
    assert attempt["weak_pairing_domain_adjusted"] is True
    assert attempt["regularity_assumptions_refined"] is True
    assert attempt["regularity_context_refined"] is True
    assert attempt["test_function_class_identified"] is True
    assert attempt["candidate_source_definition_refined"] is True
    assert attempt["scope_restriction_recorded"] is True
    assert attempt["obstruction_accounting_recorded"] is True
    assert {row["component_scope"] for row in attempt["refined_components"]} >= {
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "obstruction_accounting",
        "governance_boundary",
    }
    assert attempt["weak_pairing_domain_id"] == "toy_weak_pairing_domain_v2_candidate"
    assert attempt["regularity_structure_id"] == "toy_regular_context_v2_candidate"
    assert attempt["test_function_class_id"] == (
        "toy_conservation_test_function_class_v1_candidate"
    )
    assert attempt["candidate_source_definition_id"] == (
        "toy_source_candidate_definition_v2_candidate"
    )
    assert attempt["refined_artifact_status"] == (
        "post_retest_refined_toy_candidate_pending_result_review"
    )


def test_minimal_working_model_refinement_attempt_after_retest_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["candidate_only_status_preserved"] is True
    assert attempt["toy_source_candidate_status"] == "candidate_only_not_source_admissibility"
    assert attempt["toy_source_candidate_remains_candidate_only"] is True
    for key in [
        "toy_source_promoted_to_admissible_source",
        "conservation_retest_retried",
        "conservation_retest_executed_by_attempt",
        "conservation_retest_result_claimed",
        "conservation_retest_pass_claimed",
        "conservation_retest_failure_claimed",
        "countermodel_packet_authorized",
        "countermodel_packet_prepared",
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
        "conservation_claimed",
        "conservation_proved",
        "conservation_proof_object_constructed",
        "conservation_witness_constructed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_claimed",
        "empirical_validation_claimed",
        "scientific_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "release_assembly_authorized",
        "release_packet_assembled",
        "public_submission_authorized",
        "publication_authorized",
    ]:
        assert attempt[key] is False, key
    assert all(
        row["source_admissibility_claimed"] is False
        and row["conservation_claimed"] is False
        for row in attempt["refined_components"]
    )
    assert attempt["aggregate_lean_timeout_caveat_preserved"] is True


def test_minimal_working_model_refinement_attempt_after_retest_validation_policy() -> None:
    attempt = _json(DEFAULT_OUT)
    policy = attempt["validation_policy"]
    for key in [
        "full_pytest_required",
        "full_governance_suite_required",
        "full_aggregate_lean_required",
        "full_ci_parity_required",
        "full_security_scan_required",
        "long_running_validation_escalation_authorized",
        "timeout_rerun_loop_authorized",
    ]:
        assert policy[key] is False, key
    assert policy["timeout_recorded_as_caveat_not_rerun_instruction"] is True
    assert attempt["validation_posture"]["full_pytest"] == "not_required_for_checkpoint"
    assert (
        attempt["validation_posture"]["full_aggregate_lean"]
        == "not_required_for_checkpoint_preserved_caveat"
    )
    assert "Full pytest" in attempt["validation_caveat"]


def test_minimal_working_model_refinement_attempt_after_retest_selects_result_review_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["selected_next_target_count"] == 1
    assert attempt["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "retry_qft_gr_minimal_working_model_conservation_retest": (
            "not_authorized_pending_attempt_result_review"
        ),
        "prepare_qft_gr_minimal_working_model_countermodel_packet_after_conservation_retest": (
            "not_authorized_pending_attempt_result_review"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_refinement_attempt_after_retest_updates_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalWorkingModelRefinementAttemptAfterConservationRetest.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_CONSERVATION_"
        "RETEST_20260613_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    attempt_workstream = _workstream(registry, CONSUMED_TARGET)
    assert attempt_workstream["status"] == "paused"
    assert attempt_workstream["attempt_executed"] == "yes"
    assert attempt_workstream["bounded_refinement_attempt_executed"] == "yes"
    assert attempt_workstream["post_retest_refinement_attempt_executed"] == "yes"
    assert attempt_workstream["weak_pairing_domain_adjusted"] == "yes"
    assert attempt_workstream["regularity_assumptions_refined"] == "yes"
    assert attempt_workstream["test_function_class_identified"] == "yes"
    assert attempt_workstream["candidate_source_definition_refined"] == "yes"
    assert attempt_workstream["selected_next_target"] == NEXT_TARGET
    assert attempt_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert attempt_workstream["conservation_retest_retried"] == "no"
    assert attempt_workstream["source_admissibility_claimed"] == "no"
    assert attempt_workstream["conservation_witness_constructed"] == "no"
    assert attempt_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["refinement_attempt_after_retest_consumed"] == "yes"
    assert active_workstream["refinement_attempt_after_retest_result_review_pending"] == "yes"
    assert active_workstream["bounded_refinement_attempt_executed"] == "yes"
    assert active_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert active_workstream["conservation_retest_retried"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_refinement_attempt_after_retest_deterministic() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest(
        packet_result_review_path=REFINEMENT_AFTER_RETEST_PACKET_RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-13T00:00:00Z",
    )
    assert attempt == generated
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_ATTEMPT_PATH,
            TOE_FORMAL_PATH,
            V01_INDEX_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            ROADMAP_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            STRICT_MAP_PATH,
            SEAM_REGISTRY_PATH,
            SEAM_INVENTORY_PATH,
        ]
    )
    for token in [
        ATTEMPT_ID,
        OUTCOME_ID,
        RESULT_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        REFINEMENT_OBJECTIVE,
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "toy_weak_pairing_domain_v2_candidate",
        "toy_regular_context_v2_candidate",
        "no source admissibility",
        "no conservation proof object",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
        "not_required_for_checkpoint",
    ]:
        assert token in joined


def test_minimal_working_model_refinement_attempt_after_retest_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_gate.py"
    )
