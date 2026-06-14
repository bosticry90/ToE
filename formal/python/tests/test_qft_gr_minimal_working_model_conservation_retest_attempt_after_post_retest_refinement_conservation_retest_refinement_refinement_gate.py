from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_report import (
    ALLOWED_RESULT_CLASSIFICATIONS,
    ATTEMPT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_CLASSIFICATION,
    RETEST_CONDITION_ID,
    RETEST_RESULT,
    RETEST_STATUS,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement_report import (
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID as PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review_report import (
    OUTCOME_ID as PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as PACKET_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_minimal_working_model_conservation_retest_attempt_after_post_"
        "retest_refinement_conservation_retest_refinement_refinement_report.py"
    )
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalWorkingModelConservationRetestAttemptAfterPostRetest"
        "RefinementConservationRetestRefinementRefinement.lean"
    )
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
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


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_files_exist() -> None:
    assert DEFAULT_PACKET_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_consumes_review_and_packet() -> None:
    attempt = _json(DEFAULT_OUT)
    review = _json(DEFAULT_PACKET_RESULT_REVIEW_PATH)
    packet = _json(
        REPO_ROOT
        / attempt[
            "consumes_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement_pointer"
        ]
    )
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["executed"] is True
    assert attempt["accepted"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert attempt["consumed_target"] == CONSUMED_TARGET
    assert (
        attempt[
            "consumes_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review"
        ]
        == PACKET_RESULT_REVIEW_ID
    )
    assert review["schema_id"] == PACKET_RESULT_REVIEW_SCHEMA_ID
    assert review["outcome_id"] == PACKET_RESULT_REVIEW_OUTCOME
    assert review["result_review_classification"] == PACKET_RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == CONSUMED_TARGET
    assert packet["schema_id"] == PACKET_SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["packet_classification"] == PACKET_CLASSIFICATION


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_records_inconclusive_result() -> None:
    attempt = _json(DEFAULT_OUT)
    matrix = attempt["retest_execution_matrix"]
    condition = attempt["retest_conservation_condition"]
    assert attempt["attempt_executed"] is True
    assert attempt["bounded_conservation_retest_attempt_only"] is True
    assert (
        attempt[
            "bounded_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_executed"
        ]
        is True
    )
    assert attempt["retest_execution_status"] == RETEST_STATUS
    assert attempt["retest_result"] == RETEST_RESULT
    assert attempt["retest_passed"] is False
    assert attempt["retest_failed"] is False
    assert attempt["retest_inconclusive"] is True
    assert attempt["conservation_retest_executed"] is True
    assert attempt["conservation_retest_result_recorded"] is True
    assert attempt["conservation_retest_result_claimed"] is False
    assert condition["condition_id"] == RETEST_CONDITION_ID
    assert condition["weak_pairing_domain_id"] == "toy_weak_pairing_domain_v4_candidate"
    assert condition["regularity_structure_id"] == "toy_regular_context_v4_candidate"
    assert condition["test_function_class_id"] == (
        "toy_conservation_test_function_class_v3_candidate"
    )
    assert condition["candidate_source_definition_id"] == (
        "toy_source_candidate_definition_v4_candidate"
    )
    assert all(not row["satisfied"] for row in matrix["pass_criteria_evaluation"])
    assert all(not row["satisfied"] for row in matrix["fail_criteria_evaluation"])
    assert all(row["satisfied"] for row in matrix["inconclusive_criteria_evaluation"])
    assert len(attempt["why_inconclusive"]) >= 7
    assert attempt["toy_source_candidate_status"] == "candidate_only_not_source_admissibility"
    assert attempt["toy_source_candidate_remains_candidate_only"] is True


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    for key in [
        "conservation_retest_result_claimed",
        "conservation_retest_pass_claimed",
        "conservation_retest_failure_claimed",
        "conservation_test_retried_as_proof",
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
        "future_pass_implies_source_admissibility",
        "future_pass_implies_qft_gr_closure",
    ]:
        assert attempt[key] is False, key
    assert attempt["aggregate_lean_timeout_caveat_preserved"] is True
    assert attempt["release_index_path_not_freshly_lean_validated"] is True
    assert attempt["aggregate_lean_not_run"] is True
    assert attempt["aggregate_lean_health_claimed"] is False
    policy = attempt["validation_policy"]
    for key in [
        "full_pytest_required",
        "full_governance_suite_required",
        "full_aggregate_lean_required",
        "full_ci_parity_required",
        "full_security_scan_required",
        "long_running_validation_escalation_authorized",
        "timeout_rerun_loop_authorized",
        "aggregate_lean_health_claimed",
    ]:
        assert policy[key] is False, key


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_selects_result_review_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["result_classification"] in ALLOWED_RESULT_CLASSIFICATIONS
    assert attempt["result_classification_count"] == 1
    assert sum(1 for row in attempt["classification_rows"] if row["selected"]) == 1
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["selected_next_target_count"] == 1
    assert attempt["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        (
            "prepare_qft_gr_minimal_working_model_refinement_packet_after_"
            "post_retest_refinement_conservation_retest_refinement_refinement"
        ): "not_selected_pending_result_review",
        (
            "prepare_qft_gr_minimal_working_model_countermodel_packet_after_"
            "post_retest_refinement_conservation_retest_refinement_refinement"
        ): "not_selected_pending_result_review",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_updates_live_target() -> None:
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
        "QFTGRMinimalWorkingModelConservationRetestAttemptAfterPostRetest"
        "RefinementConservationRetestRefinementRefinement.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
        "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    attempt_workstream = _workstream(registry, CONSUMED_TARGET)
    assert attempt_workstream["status"] == "paused"
    assert (
        attempt_workstream[
            "bounded_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_executed"
        ]
        == "yes"
    )
    assert attempt_workstream["conservation_retest_executed"] == "yes"
    assert attempt_workstream["retest_result"] == RETEST_RESULT
    assert attempt_workstream["retest_inconclusive"] == "yes"
    assert attempt_workstream["conservation_retest_passed"] == "no"
    assert attempt_workstream["conservation_retest_failed"] == "no"
    assert attempt_workstream["selected_next_target"] == NEXT_TARGET
    assert attempt_workstream["source_admissibility_claimed"] == "no"
    assert attempt_workstream["conservation_witness_constructed"] == "no"
    assert attempt_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["authorized_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["retest_result"] == RETEST_RESULT
    assert active_workstream["result_review_pending"] == "yes"
    assert active_workstream["conservation_retest_executed"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_deterministic() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement(
        packet_result_review_path=DEFAULT_PACKET_RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
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
        RETEST_CONDITION_ID,
        "toy_weak_pairing_domain_v4_candidate",
        "toy_regular_context_v4_candidate",
        "toy_conservation_test_function_class_v3_candidate",
        "toy_source_candidate_definition_v4_candidate",
        "inconclusive",
        "no source admissibility",
        "no conservation proof object",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_post_retest_refinement_conservation_retest_refinement_refinement_attempt_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_gate.py"
    )

