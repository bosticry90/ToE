from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_report import (
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    RETEST_CONDITION_ID,
    SCHEMA_ID as PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_minimal_working_model_conservation_retest_packet_after_post_"
        "retest_refinement_conservation_retest_refinement_result_review_report.py"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalWorkingModelConservationRetestPacketAfterPostRetest"
        "RefinementConservationRetestRefinementResultReview.lean"
    )
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
    assert (
        review[
            "consumes_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement"
        ]
        == PACKET_ID
    )
    assert packet["schema_id"] == PACKET_SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == CONSUMED_TARGET


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_accepts_protocol() -> None:
    review = _json(DEFAULT_OUT)
    assert review["packet_result_review_accepted"] is True
    assert review["retest_packet_result_review_accepted"] is True
    assert (
        review[
            "post_retest_refinement_conservation_retest_refinement_packet_result_review_accepted"
        ]
        is True
    )
    assert review["retest_packet_consumed"] is True
    assert (
        review[
            "post_retest_refinement_conservation_retest_refinement_packet_consumed"
        ]
        is True
    )
    assert review["retest_packet_preparation_only_confirmed"] is True
    assert review["conservation_retest_packet_result_reviewed"] is True
    delta = review["newest_refinement_delta"]
    changes = {
        row["component"]: row
        for row in delta["changed_after_repeated_inconclusive_retests"]
    }
    assert changes["weak_pairing_domain"]["component_id"] == (
        "toy_weak_pairing_domain_v3_candidate"
    )
    assert changes["regularity_assumptions"]["component_id"] == (
        "toy_regular_context_v3_candidate"
    )
    assert changes["test_function_class"]["component_id"] == (
        "toy_conservation_test_function_class_v2_candidate"
    )
    assert changes["candidate_source_definition"]["component_id"] == (
        "toy_source_candidate_definition_v3_candidate"
    )
    condition = review["retest_conservation_condition"]
    assert condition["condition_id"] == RETEST_CONDITION_ID
    assert condition["weak_pairing_domain_id"] == "toy_weak_pairing_domain_v3_candidate"
    assert condition["regularity_structure_id"] == "toy_regular_context_v3_candidate"
    assert condition["test_function_class_id"] == (
        "toy_conservation_test_function_class_v2_candidate"
    )
    assert condition["candidate_source_definition_id"] == (
        "toy_source_candidate_definition_v3_candidate"
    )
    assert condition["retest_executed"] is False
    assert set(review["pass_fail_inconclusive_criteria"]) == {
        "pass",
        "fail",
        "inconclusive",
    }


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_authorizes_attempt_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["bounded_conservation_retest_attempt_authorized"] is True
    assert (
        review[
            "bounded_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_authorized"
        ]
        is True
    )
    assert review["bounded_conservation_retest_attempt_executed_by_review"] is False
    assert review["conservation_retest_executed"] is False
    assert review["conservation_retest_result_claimed"] is False
    assert review["conservation_retest_pass_claimed"] is False
    assert review["conservation_retest_failure_claimed"] is False
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selected_next_target_count"] == 1
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "bounded_conservation_retest_attempt_executed_by_review",
        "conservation_retest_executed",
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
        assert review[key] is False, key
    assert review["toy_source_candidate_remains_candidate_only"] is True
    assert review["toy_source_promoted_to_admissible_source"] is False
    assert review["aggregate_lean_timeout_caveat_preserved"] is True
    assert "Full pytest" in review["validation_caveat"]


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
    assert review["validation_posture"]["full_pytest"] == "not_required_for_checkpoint"
    assert (
        review["validation_posture"]["release_index_lean_path"]
        == "not_freshly_validated_preserved_caveat"
    )


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
        "QFTGRMinimalWorkingModelConservationRetestPacketAfterPostRetest"
        "RefinementConservationRetestRefinementResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
        "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260613_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    review_workstream = _workstream(registry, CONSUMED_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["result_review_accepted"] == "yes"
    assert review_workstream["retest_packet_result_review_accepted"] == "yes"
    assert (
        review_workstream[
            "post_retest_refinement_conservation_retest_refinement_packet_result_review_accepted"
        ]
        == "yes"
    )
    assert review_workstream["bounded_conservation_retest_attempt_authorized"] == "yes"
    assert (
        review_workstream["bounded_conservation_retest_attempt_executed_by_review"]
        == "no"
    )
    assert review_workstream["conservation_retest_executed"] == "no"
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["authorized_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["retest_packet_result_review_consumed"] == "yes"
    assert (
        active_workstream[
            "post_retest_refinement_conservation_retest_refinement_packet_result_review_consumed"
        ]
        == "yes"
    )
    assert active_workstream["bounded_conservation_retest_attempt_authorized"] == "yes"
    assert active_workstream["bounded_conservation_retest_attempt_executed"] == "no"
    assert active_workstream["conservation_retest_executed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
        packet_path=PACKET_PATH,
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
        RETEST_CONDITION_ID,
        "bounded conservation retest attempt",
        "toy_weak_pairing_domain_v3_candidate",
        "toy_regular_context_v3_candidate",
        "toy_conservation_test_function_class_v2_candidate",
        "toy_source_candidate_definition_v3_candidate",
        "no source admissibility",
        "no conservation proof object",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_post_retest_refinement_conservation_retest_refinement_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review_gate.py"
    )
