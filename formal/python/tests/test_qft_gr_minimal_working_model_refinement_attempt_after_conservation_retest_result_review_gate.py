from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_report import (
    ATTEMPT_ID as REFINEMENT_ATTEMPT_AFTER_RETEST_ID,
    DEFAULT_OUT as REFINEMENT_ATTEMPT_AFTER_RETEST_PATH,
    OUTCOME_ID as REFINEMENT_ATTEMPT_AFTER_RETEST_OUTCOME,
    REFINEMENT_OBJECTIVE,
    RESULT_CLASSIFICATION as REFINEMENT_ATTEMPT_AFTER_RETEST_CLASSIFICATION,
    SCHEMA_ID as REFINEMENT_ATTEMPT_AFTER_RETEST_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelRefinementAttemptAfterConservationRetestResultReview.lean"
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


def test_minimal_working_model_refinement_attempt_after_retest_result_review_files_exist() -> None:
    assert REFINEMENT_ATTEMPT_AFTER_RETEST_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_minimal_working_model_refinement_attempt_after_retest_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(REFINEMENT_ATTEMPT_AFTER_RETEST_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert (
        review["consumes_qft_gr_minimal_working_model_refinement_attempt_after_retest"]
        == REFINEMENT_ATTEMPT_AFTER_RETEST_ID
    )
    assert attempt["schema_id"] == REFINEMENT_ATTEMPT_AFTER_RETEST_SCHEMA_ID
    assert attempt["attempt_id"] == REFINEMENT_ATTEMPT_AFTER_RETEST_ID
    assert attempt["outcome_id"] == REFINEMENT_ATTEMPT_AFTER_RETEST_OUTCOME
    assert (
        attempt["result_classification"]
        == REFINEMENT_ATTEMPT_AFTER_RETEST_CLASSIFICATION
    )
    assert attempt["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_refinement_attempt_after_retest_result_review_accepts_refined_candidate_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["refinement_attempt_after_retest_result_review_accepted"] is True
    assert review["post_retest_refinement_attempt_result_review_accepted"] is True
    assert review["refinement_attempt_executed_confirmed"] is True
    assert review["bounded_refinement_attempt_executed"] is True
    assert review["post_retest_refinement_attempt_executed"] is True
    assert review["refined_candidate_accepted"] is True
    assert review["candidate_only_status_preserved"] is True
    assert review["toy_source_candidate_status"] == "candidate_only_not_source_admissibility"
    assert review["toy_source_candidate_remains_candidate_only"] is True
    assert review["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert review["selected_refinement_target"] == REFINEMENT_OBJECTIVE
    assert review["selected_refinement_target_count"] == 1
    assert {row["component_scope"] for row in review["refined_components"]} >= {
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "obstruction_accounting",
        "governance_boundary",
    }


def test_minimal_working_model_refinement_attempt_after_retest_result_review_authorizes_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["bounded_conservation_retest_packet_authorized"] is True
    assert review["conservation_retest_packet_preparation_authorized"] is True
    assert review["conservation_retest_packet_prepared_by_review"] is False
    assert review["conservation_retest_packet_prepared"] is False
    assert review["conservation_retest_attempt_authorized"] is False
    assert review["conservation_retest_retried"] is False
    assert review["conservation_retest_executed_by_review"] is False
    assert review["conservation_retest_result_claimed"] is False
    assert review["conservation_retest_pass_claimed"] is False
    assert review["conservation_retest_failure_claimed"] is False
    assert review["countermodel_packet_authorized"] is False
    assert review["countermodel_packet_prepared"] is False


def test_minimal_working_model_refinement_attempt_after_retest_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "toy_source_promoted_to_admissible_source",
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
        assert review[key] is False, key
    assert all(
        row["source_admissibility_claimed"] is False
        and row["conservation_claimed"] is False
        for row in review["refined_components"]
    )
    assert review["aggregate_lean_timeout_caveat_preserved"] is True
    assert "Full pytest" in review["validation_caveat"]


def test_minimal_working_model_refinement_attempt_after_retest_result_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
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
    assert review["validation_posture"]["full_pytest"] == "not_required_for_checkpoint"
    assert (
        review["validation_posture"]["full_aggregate_lean"]
        == "not_required_for_checkpoint_preserved_caveat"
    )


def test_minimal_working_model_refinement_attempt_after_retest_result_review_selects_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selected_next_target_count"] == 1
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        (
            "execute_qft_gr_minimal_working_model_conservation_retest_"
            "attempt_after_post_retest_refinement"
        ): "not_authorized_before_packet_review",
        "retry_qft_gr_minimal_working_model_conservation_retest": (
            "not_authorized_by_review_execution_not_packet"
        ),
        "prepare_qft_gr_minimal_working_model_countermodel_packet_after_conservation_retest": (
            "not_selected_no_failed_retest_obstruction"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_refinement_attempt_after_retest_result_review_updates_live_target() -> None:
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
        "QFTGRMinimalWorkingModelRefinementAttemptAfterConservationRetestResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_CONSERVATION_"
        "RETEST_RESULT_REVIEW_20260613_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    review_workstream = _workstream(registry, CONSUMED_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["result_review_accepted"] == "yes"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["bounded_conservation_retest_packet_authorized"] == "yes"
    assert review_workstream["conservation_retest_packet_prepared_by_review"] == "no"
    assert review_workstream["conservation_retest_executed_by_review"] == "no"
    assert review_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["refinement_attempt_after_retest_result_review_consumed"] == "yes"
    assert active_workstream["bounded_conservation_retest_packet_authorized"] == "yes"
    assert active_workstream["conservation_retest_packet_prepared"] == "no"
    assert active_workstream["conservation_retest_attempt_authorized"] == "no"
    assert active_workstream["conservation_retest_retried"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_refinement_attempt_after_retest_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_result_review(
        attempt_path=REFINEMENT_ATTEMPT_AFTER_RETEST_PATH,
        captured_at_utc="2026-06-13T00:00:00Z",
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_REVIEW_PATH,
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
        REVIEW_ID,
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        REFINEMENT_OBJECTIVE,
        "bounded_conservation_retest_packet_authorized",
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
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


def test_minimal_working_model_refinement_attempt_after_retest_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest_result_review_gate.py"
    )
