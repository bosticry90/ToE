from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_report import (
    DEFAULT_OUT,
    OUTCOME_ID,
    PACKET_ID,
    PACKET_TARGET,
    REVIEW_TARGET,
    build_packet,
)
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_result_review_report import (
    NEXT_TARGET as RESULT_REVIEW_NEXT_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
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
LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelDemonstrationPacket.lean"
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


def test_minimal_working_model_packet_is_deterministic_and_packet_only() -> None:
    payload = _json(DEFAULT_OUT)
    assert payload == build_packet()
    assert payload["packet_id"] == PACKET_ID
    assert payload["consumed_target"] == PACKET_TARGET
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["selected_next_target"] == REVIEW_TARGET
    assert payload["selection_count"] == 1
    assert payload["packet_preparation_only"] is True
    assert payload["model_execution_authorized"] is False
    assert payload["toy_source_candidate"]["source_admissibility_claimed"] is False
    assert payload["admissibility_candidate_only"]["source_map_closure_claimed"] is False
    assert payload["conservation_test_target"]["conservation_proved"] is False
    assert payload["conservation_test_target"]["conservation_witness_constructed"] is False
    for value in payload["acceptance_criteria"].values():
        assert value is True
    for key, value in payload["non_claim_boundary"].items():
        assert value is False, key


def test_minimal_working_model_packet_contains_required_scope_fields() -> None:
    payload = _json(DEFAULT_OUT)
    for field in [
        "minimal_model_scope",
        "toy_source_candidate",
        "simplified_field_state_setup",
        "background_geometry_assumptions",
        "source_like_object_criteria",
        "admissibility_candidate_only",
        "imported_regularities",
        "conservation_test_target",
        "failure_modes",
        "countermodel_hooks",
        "falsifier_hooks",
        "claim_level",
        "claim_ceiling",
    ]:
        assert field in payload
    assert "MR-ASSUMP-004-limit_interchange_regularization_boundary" in payload[
        "imported_regularities"
    ]
    assert "QFT_GR_COUNTERMODEL_002_EXPECTATION_NOT_CONSERVED" in payload[
        "countermodel_hooks"
    ]
    assert "QFT-GR weak/strong conservation falsifier" in payload["falsifier_hooks"]


def test_minimal_working_model_packet_preserves_historical_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET)
    state = registry["current_target_state"]
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1
    active_workstream = active[0]

    assert state["previous_live_next_target"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert state["live_next_target"] == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    assert state["active_lane"] == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalWorkingModelConservationTestAttempt.lean"
    )
    assert PACKET_TARGET in registry["next_strict_target_coverage"]
    assert REVIEW_TARGET in registry["next_strict_target_coverage"]
    assert RESULT_REVIEW_NEXT_TARGET in registry["next_strict_target_coverage"]
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

    assert active_workstream["workstream_id"] == (
        CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        active_workstream["authorized_next_strict_target"]
        == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert active_workstream["authorization_evidence"] == state["live_next_target_evidence"]
    assert active_workstream["report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_20260612_v0.json"
    )
    assert active_workstream["outcome_id"] == CONSERVATION_TEST_ATTEMPT_OUTCOME
    assert active_workstream["conservation_test_attempt_consumed"] == "yes"
    assert active_workstream["conservation_test_executed"] == "yes"
    assert active_workstream["test_inconclusive"] == "yes"

    packet_workstream = _workstream(registry, PACKET_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["selected_next_target"] == REVIEW_TARGET
    assert packet_workstream["model_execution_authorized"] == "no"

    review_workstream = _workstream(registry, REVIEW_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["packet_result_review_accepted"] == "yes"
    assert review_workstream["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET

    packet_result_review_workstream = _workstream(registry, FINAL_LIVE_TARGET)
    assert packet_result_review_workstream["status"] == "paused"
    assert packet_result_review_workstream["selected_next_target"] == (
        CONSERVATION_TEST_ATTEMPT_TARGET
    )
    assert packet_result_review_workstream["packet_result_review_accepted"] == "yes"

    conservation_test_attempt_workstream = _workstream(
        registry, CONSERVATION_TEST_ATTEMPT_TARGET
    )
    assert conservation_test_attempt_workstream["status"] == "paused"
    assert conservation_test_attempt_workstream["selected_next_target"] == (
        CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert conservation_test_attempt_workstream["conservation_test_executed"] == "yes"
    assert conservation_test_attempt_workstream["test_inconclusive"] == "yes"


def test_minimal_working_model_packet_has_lean_and_public_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            LEAN_PATH,
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
        PACKET_TARGET,
        REVIEW_TARGET,
        RESULT_REVIEW_NEXT_TARGET,
        CONSTRUCTION_ATTEMPT_RESULT_REVIEW_TARGET,
        CANDIDATE_ANALYSIS_TARGET,
        CANDIDATE_ANALYSIS_RESULT_REVIEW_TARGET,
        CONSERVATION_TEST_PACKET_TARGET,
        FINAL_LIVE_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest_refinement_result",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined

    frontier = _read(FRONTIER_PATH)
    assert RESULT_REVIEW_NEXT_TARGET in frontier
    assert CONSTRUCTION_ATTEMPT_RESULT_REVIEW_TARGET in frontier
    assert CANDIDATE_ANALYSIS_TARGET in frontier
    assert CANDIDATE_ANALYSIS_RESULT_REVIEW_TARGET in frontier
    assert CONSERVATION_TEST_PACKET_TARGET in frontier
    assert (
        'def currentLiveNextStrictTargetV0 : String :=\n'
        f'  "{CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET}"'
        in frontier
        or 'def currentLiveNextStrictTargetV0 : String :=\n'
        '  "prepare_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_refinement"'
        in frontier
    )


def test_minimal_working_model_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_demonstration_packet_gate.py"
    )
