from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_report import (
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_TARGET,
)
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_result_review_report import (
    AGGREGATE_LEAN_TIMEOUT_CAVEAT,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_minimal_working_model_demonstration_packet_result_review,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_report import (
    NEXT_TARGET as FINAL_LIVE_TARGET,
    OUTCOME_ID as CONSERVATION_TEST_PACKET_OUTCOME,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_result_review_report import (
    NEXT_TARGET as CONSERVATION_TEST_ATTEMPT_TARGET,
    OUTCOME_ID as CONSERVATION_TEST_PACKET_RESULT_REVIEW_OUTCOME,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_attempt_report import (
    NEXT_TARGET as CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET,
    OUTCOME_ID as CONSERVATION_TEST_ATTEMPT_OUTCOME,
)
from formal.python.tools.qft_gr_post_mr_assump004_governed_maturation_reports import (
    CAPTURED_AT_UTC,
)


CONSTRUCTION_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_construction_attempt_result"
)
CANDIDATE_ANALYSIS_TARGET = "analyze_qft_gr_minimal_working_model_candidate_only"
CANDIDATE_ANALYSIS_RESULT_REVIEW_TARGET = (
    "review_qft_gr_minimal_working_model_candidate_analysis_result"
)
CONSERVATION_TEST_PACKET_TARGET = (
    "prepare_qft_gr_minimal_working_model_conservation_test_packet"
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_demonstration_packet_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelDemonstrationPacketResultReview.lean"
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


def test_minimal_working_model_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_minimal_working_model_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert (
        review["consumes_qft_gr_minimal_working_model_demonstration_packet"]
        == PACKET_ID
    )
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert review["consumed_packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == REVIEW_TARGET
    assert review["consumed_target"] == REVIEW_TARGET


def test_minimal_working_model_packet_result_review_confirms_scope_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["packet_preparation_only_confirmed_by_review"] is True
    assert review["minimal_model_scope_bounded"] is True
    assert review["toy_source_candidate_status"] == (
        "candidate_only_not_source_admissibility"
    )
    assert review["toy_source_candidate_remains_candidate_only"] is True
    assert review["bounded_model_construction_attempt_authorized"] is True
    assert review["bounded_model_construction_attempt_executed_by_review"] is False
    assert review["minimal_model_demonstration_executed_by_review"] is False
    assert review["model_execution_authorized_by_review"] is False


def test_minimal_working_model_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
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
    assert review["validation_caveat"] == AGGREGATE_LEAN_TIMEOUT_CAVEAT


def test_minimal_working_model_packet_result_review_selects_one_next_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selection_count"] == 1
    assert review["packet_result_review_selected_target_split_preserved"] is True
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        REVIEW_TARGET: "completed_consumed_live_target",
        "execute_qft_gr_minimal_working_model_demonstration": (
            "not_authorized_without_construction_attempt"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_packet_result_review_updates_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET)
    state = registry["current_target_state"]
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert state["live_next_target"] == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    assert state["active_lane"] == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    assert REVIEW_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSTRUCTION_ATTEMPT_RESULT_REVIEW_TARGET in registry[
        "next_strict_target_coverage"
    ]
    assert CANDIDATE_ANALYSIS_TARGET in registry["next_strict_target_coverage"]
    assert CANDIDATE_ANALYSIS_RESULT_REVIEW_TARGET in registry[
        "next_strict_target_coverage"
    ]
    assert CONSERVATION_TEST_PACKET_TARGET in registry["next_strict_target_coverage"]
    assert FINAL_LIVE_TARGET in registry["next_strict_target_coverage"]
    assert CONSERVATION_TEST_ATTEMPT_TARGET in registry["next_strict_target_coverage"]
    assert (
        CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
        in registry["next_strict_target_coverage"]
    )

    review_workstream = _workstream(registry, REVIEW_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["packet_result_review_accepted"] == "yes"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["bounded_model_construction_attempt_authorized"] == "yes"
    assert review_workstream["bounded_model_construction_attempt_executed"] == "no"

    construction_workstream = _workstream(registry, NEXT_TARGET)
    assert construction_workstream["status"] == "paused"
    assert construction_workstream["selected_next_target"] == (
        CONSTRUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert construction_workstream["bounded_model_construction_attempt_executed"] == "yes"
    assert construction_workstream["source_admissibility_claimed"] == "no"
    assert construction_workstream["qft_gr_closure_claimed"] == "no"

    result_review_workstream = _workstream(
        registry, CONSTRUCTION_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert result_review_workstream["status"] == "paused"
    assert result_review_workstream["selected_next_target"] == CANDIDATE_ANALYSIS_TARGET
    assert result_review_workstream["model_analysis_only_authorized"] == "yes"
    assert result_review_workstream["model_analysis_executed_by_review"] == "no"

    analysis_workstream = _workstream(registry, CANDIDATE_ANALYSIS_TARGET)
    assert analysis_workstream["status"] == "paused"
    assert analysis_workstream["selected_next_target"] == (
        CANDIDATE_ANALYSIS_RESULT_REVIEW_TARGET
    )
    assert analysis_workstream["analysis_completed"] == "yes"

    candidate_analysis_result_review_workstream = _workstream(
        registry, CANDIDATE_ANALYSIS_RESULT_REVIEW_TARGET
    )
    assert candidate_analysis_result_review_workstream["status"] == "paused"
    assert (
        candidate_analysis_result_review_workstream["selected_next_target"]
        == CONSERVATION_TEST_PACKET_TARGET
    )
    assert (
        candidate_analysis_result_review_workstream["result_review_accepted"]
        == "yes"
    )
    assert (
        candidate_analysis_result_review_workstream[
            "bounded_conservation_test_packet_authorized"
        ]
        == "yes"
    )

    conservation_packet_workstream = _workstream(registry, CONSERVATION_TEST_PACKET_TARGET)
    assert conservation_packet_workstream["status"] == "paused"
    assert conservation_packet_workstream["selected_next_target"] == FINAL_LIVE_TARGET
    assert conservation_packet_workstream["packet_prepared"] == "yes"
    assert conservation_packet_workstream["conservation_test_executed"] == "no"

    packet_result_review_workstream = _workstream(registry, FINAL_LIVE_TARGET)
    assert packet_result_review_workstream["status"] == "paused"
    assert packet_result_review_workstream["selected_next_target"] == (
        CONSERVATION_TEST_ATTEMPT_TARGET
    )
    assert packet_result_review_workstream["packet_result_review_accepted"] == "yes"
    assert (
        packet_result_review_workstream[
            "bounded_conservation_test_attempt_authorized"
        ]
        == "yes"
    )

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == (
        CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert active_workstream["outcome_id"] == CONSERVATION_TEST_ATTEMPT_OUTCOME
    assert active_workstream["conservation_test_attempt_consumed"] == "yes"
    assert active_workstream["conservation_test_executed"] == "yes"
    assert active_workstream["test_inconclusive"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_demonstration_packet_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=CAPTURED_AT_UTC,
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
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
        REVIEW_TARGET,
        NEXT_TARGET,
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no empirical validation",
        "no public submission",
    ]:
        assert token in joined


def test_minimal_working_model_packet_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_demonstration_packet_result_review_gate.py"
    )
