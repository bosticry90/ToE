from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_obstruction_class_stabilization_report import (
    CANONICAL_OBSTRUCTION_ID,
    CONSUMED_TARGET,
    DEFAULT_MARKDOWN_OUT,
    DEFAULT_OUT,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PATTERN_STABILIZATION_SIGNAL,
    POSITIVE_WITNESS_TARGET,
    SCHEMA_ID,
    STATUS,
    build_qft_gr_minimal_model_obstruction_class_stabilization_packet,
    render_markdown,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    REVIEW_ID as RESULT_REVIEW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_model_obstruction_class_stabilization_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelObstructionClassStabilization.lean"
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


def test_qft_gr_minimal_model_obstruction_class_stabilization_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert DEFAULT_MARKDOWN_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_minimal_model_obstruction_class_stabilization_consumes_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert (
        packet[
            "consumes_qft_gr_minimal_working_model_conservation_retest_result_review"
        ]
        == RESULT_REVIEW_ID
    )
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_qft_gr_minimal_model_obstruction_class_stabilization_compresses_chain() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["all_prior_conservation_attempts_consumed"] is True
    assert packet["attempt_chain_count"] == 5
    assert packet["latest_result_marked_inconclusive"] is True
    assert all(row["inconclusive"] for row in packet["attempt_chain_rows"])
    assert not any(row["converted_to_pass"] for row in packet["attempt_chain_rows"])
    assert not any(row["converted_to_failure"] for row in packet["attempt_chain_rows"])
    required = {
        "what_changed",
        "what_was_tested",
        "what_remained_undecided",
        "why_not_conservation_proof",
        "why_not_failure",
        "local_validation_result",
    }
    assert all(required <= set(row) for row in packet["attempt_chain_rows"])


def test_qft_gr_minimal_model_obstruction_class_stabilization_obstruction_map() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert packet["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert packet["obstruction_status"] == STATUS
    assert packet["dominant_obstruction_candidate_selected"] is True
    assert packet["dominant_obstruction_resolved"] is False
    assert packet["mathematical_resolution_claimed"] is False
    selected = [row for row in packet["obstruction_map_rows"] if row["selected"]]
    assert len(selected) == 1
    assert selected[0]["obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert selected[0]["resolved"] is False
    assert packet["supporting_obstruction_count"] == 7
    assert all(row["resolved"] is False for row in packet["obstruction_map_rows"])
    assert packet["pattern_stabilization_signal"] == PATTERN_STABILIZATION_SIGNAL


def test_qft_gr_minimal_model_obstruction_class_stabilization_preserves_boundaries() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["immediate_retest_authorized"] is False
    assert packet["conservation_retest_rerun_authorized"] is False
    assert packet["ordinary_model_refinement_authorized"] is False
    assert packet["positive_witness_lane_recommended"] is True
    assert packet["recommended_next_lane_after_review"] == POSITIVE_WITNESS_TARGET
    assert packet["countermodel_lane_retained_as_follow_on"] is True
    assert packet["source_map_ladder_lane_retained_as_follow_on"] is True
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
        assert packet[key] is False, key


def test_qft_gr_minimal_model_obstruction_class_stabilization_selects_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_count"] == 1
    decisions = {row["target"]: row["decision"] for row in packet["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[POSITIVE_WITNESS_TARGET] == "recommended_after_packet_review"
    assert decisions[
        "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement"
    ] == "not_authorized"
    assert decisions[
        "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_refinement"
    ] == "not_authorized"


def test_qft_gr_minimal_model_obstruction_class_stabilization_updates_live_target() -> None:
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
        "QFTGRMinimalModelObstructionClassStabilization.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    packet_workstream = _workstream(registry, CONSUMED_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["packet_prepared"] == "yes"
    assert packet_workstream["selected_next_target"] == NEXT_TARGET
    assert packet_workstream["dominant_obstruction_candidate"] == (
        DOMINANT_OBSTRUCTION_CANDIDATE
    )
    assert packet_workstream["dominant_obstruction_resolved"] == "no"
    assert packet_workstream["immediate_retest_authorized"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["result_review_pending"] == "yes"
    assert active_workstream["positive_witness_lane_recommended"] == "yes"
    assert active_workstream["immediate_retest_authorized"] == "no"
    assert active_workstream["ordinary_model_refinement_authorized"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_qft_gr_minimal_model_obstruction_class_stabilization_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_model_obstruction_class_stabilization_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
    )
    assert packet == generated
    assert _read(DEFAULT_MARKDOWN_OUT) == render_markdown(packet)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            DEFAULT_MARKDOWN_OUT,
            LEAN_PACKET_PATH,
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
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DOMINANT_OBSTRUCTION_CANDIDATE,
        CANONICAL_OBSTRUCTION_ID,
        PATTERN_STABILIZATION_SIGNAL,
        POSITIVE_WITNESS_TARGET,
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_qft_gr_minimal_model_obstruction_class_stabilization_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_obstruction_class_stabilization_gate.py"
    )
