from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_result_review_report import (
    DEFAULT_OUT as CURRENT_REVIEW_PATH,
    OUTCOME_ID as CURRENT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as CURRENT_REVIEW_CLASSIFICATION,
    REVIEW_ID as CURRENT_REVIEW_ID,
    SCHEMA_ID as CURRENT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBSTRUCTION_CLASS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REFINEMENT_OBJECTIVE,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelRefinementPacketAfterPostRetestRefinementConservationRetest.lean"
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


def test_post_retest_refinement_conservation_retest_refinement_packet_files_exist() -> None:
    assert CURRENT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_post_retest_refinement_conservation_retest_refinement_packet_consumes_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(CURRENT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["accepted"] is True
    assert packet["packet_prepared"] is True
    assert packet["packet_preparation_only"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["consumes_current_result_review"] == CURRENT_REVIEW_ID
    assert review["schema_id"] == CURRENT_REVIEW_SCHEMA_ID
    assert review["outcome_id"] == CURRENT_REVIEW_OUTCOME
    assert review["result_review_classification"] == CURRENT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_post_retest_refinement_conservation_retest_refinement_packet_records_repeated_inconclusive_signal() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["obstruction_class"] == OBSTRUCTION_CLASS
    assert packet["repeated_inconclusive_signal_count"] == 2
    assert len(packet["why_refinement_not_immediate_retest"]) >= 4
    assert packet["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert packet["selected_refinement_target"] == REFINEMENT_OBJECTIVE
    assert packet["selected_refinement_target_count"] == 1
    assert packet["refinement_focus"] == (
        "repeat_inconclusive_weak_divergence_pairing_domain_regular_context_"
        "test_function_candidate_definition_scope_restriction"
    )
    assert set(packet["identified_refinement_scopes"]) >= {
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "obstruction_accounting",
        "validation_boundary",
    }
    assert packet["current_weak_pairing_domain_id"] == "toy_weak_pairing_domain_v2_candidate"
    assert packet["current_regular_context_id"] == "toy_regular_context_v2_candidate"
    assert packet["proposed_weak_pairing_domain_revision"] == (
        "toy_weak_pairing_domain_v3_candidate"
    )
    assert packet["proposed_regular_context_revision"] == "toy_regular_context_v3_candidate"
    for row in packet["refinement_dimensions"]:
        assert row["obstruction_class"] == OBSTRUCTION_CLASS
        assert row["source_admissibility_claimed"] is False
        assert row["conservation_claimed"] is False


def test_post_retest_refinement_conservation_retest_refinement_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "model_refinement_executed",
        "refinement_attempt_executed",
        "countermodel_packet_authorized",
        "countermodel_packet_prepared",
        "conservation_retest_retried",
        "conservation_retest_executed_by_packet",
        "conservation_retest_result_claimed",
        "conservation_retest_pass_claimed",
        "conservation_retest_failure_claimed",
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
        assert packet[key] is False, key
    assert packet["toy_source_candidate_remains_candidate_only"] is True
    assert packet["aggregate_lean_timeout_caveat_preserved"] is True
    assert packet["bounded_lean_substitute_passed_prior_checkpoint"] is True
    assert packet["targeted_review_frontier_index_timed_out_preserved"] is True
    assert packet["release_index_path_not_freshly_lean_validated"] is True
    assert packet["aggregate_lean_not_run"] is True
    assert "release-index path is not freshly Lean-validated" in packet["validation_caveat"]
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
        assert packet["validation_policy"][key] is False, key


def test_post_retest_refinement_conservation_retest_refinement_packet_selects_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_next_target_count"] == 1
    assert packet["selection_count"] == 1
    decisions = {row["target"]: row["decision"] for row in packet["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[CONSUMED_TARGET] == "completed_consumed_live_target"
    assert (
        decisions[
            "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement"
        ]
        == "not_authorized_without_new_refinement_attempt"
    )
    assert (
        decisions[
            "prepare_qft_gr_minimal_working_model_countermodel_packet_after_post_retest_refinement_conservation_retest"
        ]
        == "not_selected_no_failed_retest_obstruction"
    )
    assert decisions["claim_qft_gr_source_admissibility"] == "not_authorized"
    assert decisions["prove_qft_gr_conservation"] == "not_authorized"
    assert decisions["close_qft_gr_seam"] == "not_authorized"


def test_post_retest_refinement_conservation_retest_refinement_packet_updates_live_target() -> None:
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
        "QFTGRMinimalWorkingModelRefinementPacketAfterPostRetestRefinementConservationRetest.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
        "REFINEMENT_CONSERVATION_RETEST_20260613_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    packet_workstream = _workstream(registry, CONSUMED_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["packet_prepared"] == "yes"
    assert packet_workstream["packet_preparation_only"] == "yes"
    assert packet_workstream["selected_next_target"] == NEXT_TARGET
    assert packet_workstream["obstruction_class"] == OBSTRUCTION_CLASS
    assert packet_workstream["repeated_inconclusive_signal_recorded"] == "yes"
    assert packet_workstream["conservation_retest_retried"] == "no"
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["conservation_witness_constructed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["refinement_packet_consumed"] == "yes"
    assert active_workstream["refinement_packet_result_review_pending"] == "yes"
    assert active_workstream["obstruction_class"] == OBSTRUCTION_CLASS
    assert active_workstream["conservation_retest_retried"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_post_retest_refinement_conservation_retest_refinement_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest(
        current_review_path=CURRENT_REVIEW_PATH,
        captured_at_utc="2026-06-13T00:00:00Z",
    )
    assert packet == generated
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
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
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        REFINEMENT_OBJECTIVE,
        OBSTRUCTION_CLASS,
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_post_retest_refinement_conservation_retest_refinement_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_gate.py"
    )
