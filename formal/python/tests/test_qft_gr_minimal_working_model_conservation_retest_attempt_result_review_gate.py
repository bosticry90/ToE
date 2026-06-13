from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_report import (
    ATTEMPT_ID as CONSERVATION_RETEST_ATTEMPT_ID,
    DEFAULT_OUT as CONSERVATION_RETEST_ATTEMPT_PATH,
    OUTCOME_ID as CONSERVATION_RETEST_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as CONSERVATION_RETEST_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as CONSERVATION_RETEST_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_result_review_report import (
    CONSUMED_TARGET,
    COUNTERMODEL_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    SELECTED_REFINEMENT_TARGET,
    build_qft_gr_minimal_working_model_conservation_retest_attempt_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_conservation_retest_attempt_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelConservationRetestAttemptResultReview.lean"
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


def test_minimal_working_model_conservation_retest_attempt_result_review_files_exist() -> None:
    assert CONSERVATION_RETEST_ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_minimal_working_model_conservation_retest_attempt_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(CONSERVATION_RETEST_ATTEMPT_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert (
        review["consumes_qft_gr_minimal_working_model_conservation_retest_attempt"]
        == CONSERVATION_RETEST_ATTEMPT_ID
    )
    assert attempt["schema_id"] == CONSERVATION_RETEST_ATTEMPT_SCHEMA_ID
    assert attempt["attempt_id"] == CONSERVATION_RETEST_ATTEMPT_ID
    assert attempt["outcome_id"] == CONSERVATION_RETEST_ATTEMPT_OUTCOME
    assert attempt["result_classification"] == CONSERVATION_RETEST_ATTEMPT_CLASSIFICATION
    assert attempt["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_conservation_retest_attempt_result_review_accepts_inconclusive_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["conservation_retest_attempt_result_review_accepted"] is True
    assert review["classification_confirmed"] is True
    assert review["accepted_inconclusive_result"] is True
    assert review["inconclusive_not_converted_to_pass"] is True
    assert review["inconclusive_not_converted_to_failure"] is True
    assert review["retest_result"] == "inconclusive"
    assert review["retest_passed"] is False
    assert review["retest_failed"] is False
    assert review["retest_inconclusive"] is True
    assert review["conservation_retest_passed"] is False
    assert review["conservation_retest_failed"] is False
    assert review["conservation_retest_inconclusive"] is True


def test_minimal_working_model_conservation_retest_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
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
    assert review["aggregate_lean_timeout_caveat_preserved"] is True
    assert "full lake build ToeFormal timed out" in review["validation_caveat"]


def test_minimal_working_model_conservation_retest_attempt_result_review_selects_one_next_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selected_next_target_count"] == 1
    assert review["selection_count"] == 1
    assert review["model_refinement_packet_authorized"] is True
    assert review["model_refinement_packet_prepared_by_review"] is False
    assert review["model_refinement_executed_by_review"] is False
    assert review["countermodel_packet_authorized"] is False
    assert review["countermodel_packet_prepared_by_review"] is False
    assert review["selected_refinement_target"] == SELECTED_REFINEMENT_TARGET
    assert review["selected_refinement_target_count"] == 1
    assert review["selected_refinement_or_countermodel_route"] == NEXT_TARGET
    assert review["selected_refinement_or_countermodel_route_count"] == 1
    assert sum(1 for row in review["route_rows"] if row["selected"]) == 1
    assert sum(1 for row in review["refinement_target_rows"] if row["selected"]) == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        COUNTERMODEL_TARGET: "not_selected_no_failure_obstruction",
        "retry_qft_gr_minimal_working_model_conservation_retest_as_proof": (
            "not_authorized"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_conservation_retest_attempt_result_review_updates_live_target() -> None:
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
        "QFTGRMinimalWorkingModelConservationRetestAttemptResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_RESULT_REVIEW_"
        "20260613_v0.json"
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
    assert review_workstream["conservation_retest_attempt_result_review_executed"] == "yes"
    assert review_workstream["retest_inconclusive"] == "yes"
    assert review_workstream["conservation_retest_passed"] == "no"
    assert review_workstream["conservation_retest_failed"] == "no"
    assert review_workstream["model_refinement_packet_authorized"] == "yes"
    assert review_workstream["countermodel_packet_authorized"] == "no"
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["conservation_retest_attempt_result_review_consumed"] == "yes"
    assert active_workstream["model_refinement_packet_authorized"] == "yes"
    assert active_workstream["model_refinement_packet_prepared"] == "no"
    assert active_workstream["countermodel_packet_authorized"] == "no"
    assert active_workstream["selected_refinement_target"] == SELECTED_REFINEMENT_TARGET
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_conservation_retest_attempt_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_conservation_retest_attempt_result_review(
        attempt_path=CONSERVATION_RETEST_ATTEMPT_PATH,
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
        SELECTED_REFINEMENT_TARGET,
        "qft_gr_minimal_working_model_conservation_retest_inconclusive_requires_model_refinement",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_minimal_working_model_conservation_retest_attempt_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_conservation_retest_attempt_result_review_gate.py"
    )
