from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_result_review_report import (
    DEFAULT_OUT as CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_PATH,
    OUTCOME_ID as CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_ID,
    SCHEMA_ID as CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_conservation_retest_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REFINEMENT_OBJECTIVE,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_refinement_packet_after_conservation_retest_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelRefinementPacketAfterConservationRetest.lean"
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


def test_minimal_working_model_refinement_packet_after_retest_files_exist() -> None:
    assert CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_minimal_working_model_refinement_packet_after_retest_consumes_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["accepted"] is True
    assert packet["packet_prepared"] is True
    assert packet["packet_preparation_only"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert (
        packet[
            "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_result_review"
        ]
        == CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_ID
    )
    assert review["schema_id"] == CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_SCHEMA_ID
    assert review["outcome_id"] == CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_OUTCOME
    assert (
        review["result_review_classification"]
        == CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_CLASSIFICATION
    )
    assert review["selected_next_target"] == CONSUMED_TARGET
    assert (
        packet["consumed_retest_attempt_classification"]
        == "qft_gr_minimal_working_model_conservation_retest_inconclusive_requires_model_refinement"
    )


def test_minimal_working_model_refinement_packet_after_retest_identifies_scope() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["accepted_inconclusive_retest_result"] is True
    assert packet["inconclusive_retest_not_converted_to_pass"] is True
    assert packet["inconclusive_retest_not_converted_to_failure"] is True
    assert packet["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert packet["selected_refinement_target"] == REFINEMENT_OBJECTIVE
    assert packet["selected_refinement_target_count"] == 1
    assert packet["refinement_focus"] == (
        "weak_pairing_domain_regular_context_test_function_class_"
        "candidate_definition_scope_restriction_after_inconclusive_retest"
    )
    assert set(packet["identified_refinement_scopes"]) >= {
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "obstruction_accounting",
        "governance_boundary",
    }
    assert packet["weak_pairing_domain_id"] == "toy_weak_pairing_domain_v1"
    assert packet["regularity_structure_id"] == "toy_regular_context_v1"
    assert packet["proposed_weak_pairing_domain_revision"] == (
        "toy_weak_pairing_domain_v2_candidate"
    )
    assert packet["proposed_regular_context_revision"] == (
        "toy_regular_context_v2_candidate"
    )
    assert len(packet["review_gate_requirements"]) >= 12
    for row in packet["refinement_dimensions"]:
        assert row["source_admissibility_claimed"] is False
        assert row["conservation_claimed"] is False


def test_minimal_working_model_refinement_packet_after_retest_preserves_nonclaims() -> None:
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
    ]:
        assert packet[key] is False, key
    assert packet["toy_source_candidate_remains_candidate_only"] is True
    assert packet["aggregate_lean_timeout_caveat_preserved"] is True
    assert "full lake build ToeFormal timed out" in packet["validation_caveat"]


def test_minimal_working_model_refinement_packet_after_retest_selects_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_next_target_count"] == 1
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "execute_qft_gr_minimal_working_model_refinement_attempt_after_conservation_retest": (
            "not_authorized_before_packet_result_review"
        ),
        "retry_qft_gr_minimal_working_model_conservation_retest": (
            "not_authorized_before_refinement_attempt"
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


def test_minimal_working_model_refinement_packet_after_retest_updates_live_target() -> None:
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
        "QFTGRMinimalWorkingModelRefinementPacketAfterConservationRetest.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_AFTER_CONSERVATION_RETEST_"
        "PACKET_20260613_v0.json"
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
    assert packet_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert packet_workstream["review_gate_requirements_recorded"] == "yes"
    assert packet_workstream["model_refinement_packet_prepared"] == "yes"
    assert packet_workstream["conservation_retest_retried"] == "no"
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["conservation_witness_constructed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["refinement_after_retest_packet_consumed"] == "yes"
    assert active_workstream["refinement_after_retest_packet_result_review_pending"] == "yes"
    assert active_workstream["refinement_objective"] == REFINEMENT_OBJECTIVE
    assert active_workstream["conservation_retest_retried"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_refinement_packet_after_retest_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest(
        result_review_path=CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_PATH,
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
        "weak_pairing_domain",
        "regularity_assumptions",
        "test_function_class",
        "candidate_source_definition",
        "scope_restriction",
        "qft_gr_minimal_working_model_conservation_retest_inconclusive_requires_model_refinement",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_minimal_working_model_refinement_packet_after_retest_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_refinement_packet_after_conservation_retest_gate.py"
    )
