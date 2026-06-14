from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_report import (
    DEFAULT_OUT as PACKET_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_CLASS,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REFINEMENT_OBJECTIVE,
    SCHEMA_ID as PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
        "refinement_conservation_retest_refinement_result_review_report.py"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalWorkingModelRefinementPacketAfterPostRetestRefinement"
        "ConservationRetestRefinementResultReview.lean"
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


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert CONSUMED_TARGET == EXPECTED_CONSUMED_TARGET
    assert (
        review[
            "consumes_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement"
        ]
        == PACKET_ID
    )
    assert packet["schema_id"] == PACKET_SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == CONSUMED_TARGET


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_accepts_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["refinement_packet_result_review_accepted"] is True
    assert review["packet_preparation_only_confirmed"] is True
    assert review["v3_repeated_inconclusive_signal_confirmed"] is True
    assert review["obstruction_class"] == OBSTRUCTION_CLASS
    assert review["obstruction_class_confirmed"] is True
    assert review["candidate_only_status_preserved"] is True
    assert review["toy_source_candidate_status"] == "candidate_only_not_source_admissibility"
    assert review["toy_source_candidate_remains_candidate_only"] is True
    assert review["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert review["selected_refinement_target"] == REFINEMENT_OBJECTIVE
    assert review["selected_refinement_target_count"] == 1
    assert set(review["identified_refinement_scopes"]) >= {
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "obstruction_accounting",
        "validation_boundary",
    }
    assert review["proposed_weak_pairing_domain_revision"] == (
        "toy_weak_pairing_domain_v4_candidate"
    )
    assert review["proposed_regular_context_revision"] == "toy_regular_context_v4_candidate"


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_authorizes_attempt_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["bounded_refinement_attempt_authorized"] is True
    assert review["refinement_attempt_authorized"] is True
    assert review["bounded_refinement_attempt_executed_by_review"] is False
    assert review["bounded_refinement_attempt_executed"] is False
    assert review["refinement_attempt_executed"] is False
    assert review["model_refinement_executed_by_review"] is False
    assert review["conservation_retest_retried"] is False
    assert review["conservation_retest_executed_by_review"] is False
    assert review["conservation_retest_result_claimed"] is False
    assert review["countermodel_packet_authorized"] is False
    assert review["countermodel_packet_prepared"] is False


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_preserves_nonclaims() -> None:
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
        "aggregate_lean_health_claimed",
    ]:
        assert review[key] is False, key
    assert review["release_index_path_not_freshly_lean_validated"] is True
    assert review["aggregate_lean_not_run"] is True
    assert "aggregate Lean is not run" in review["validation_caveat"]


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_validation_policy() -> None:
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
        "aggregate_lean_health_claimed",
    ]:
        assert policy[key] is False, key
    assert policy["timeout_recorded_as_caveat_not_rerun_instruction"] is True
    assert policy["release_index_path_not_freshly_lean_validated"] is True
    assert policy["aggregate_lean_not_run"] is True


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_selects_attempt_only() -> None:
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
            "execute_qft_gr_minimal_working_model_conservation_retest_attempt_"
            "after_post_retest_refinement_conservation_retest_refinement"
        ): "not_authorized_before_new_refinement_attempt",
        (
            "prepare_qft_gr_minimal_working_model_countermodel_packet_after_"
            "post_retest_refinement_conservation_retest_refinement"
        ): "not_selected_no_failed_retest_obstruction",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_updates_live_target() -> None:
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
        "QFTGRMinimalWorkingModelRefinementPacketAfterPostRetestRefinement"
        "ConservationRetestRefinementResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
        "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260614_v0.json"
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
    assert review_workstream["bounded_refinement_attempt_authorized"] == "yes"
    assert review_workstream["bounded_refinement_attempt_executed_by_review"] == "no"
    assert review_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert review_workstream["obstruction_class"] == OBSTRUCTION_CLASS
    assert review_workstream["conservation_retest_retried"] == "no"
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["authorized_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["refinement_packet_result_review_consumed"] == "yes"
    assert active_workstream["bounded_refinement_attempt_authorized"] == "yes"
    assert active_workstream["bounded_refinement_attempt_executed"] == "no"
    assert active_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert active_workstream["obstruction_class"] == OBSTRUCTION_CLASS
    assert active_workstream["conservation_retest_retried"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
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
        OBSTRUCTION_CLASS,
        "toy_weak_pairing_domain_v4_candidate",
        "toy_regular_context_v4_candidate",
        "bounded target-relevant validation",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review_gate.py"
    )
