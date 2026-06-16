from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_obstruction_class_stabilization_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    REVIEW_ID as RESULT_REVIEW_ID,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_report import (
    ATTEMPT_TARGET,
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
    POSITIVE_WITNESS_BRIDGE_LAW,
    SCHEMA_ID,
    build_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions,
    render_markdown,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalPositiveConservationWitnessPacketUnderStrictToyAssumptions.lean"
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


def test_qft_gr_minimal_positive_conservation_witness_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert DEFAULT_MARKDOWN_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_minimal_positive_conservation_witness_packet_consumes_result_review() -> None:
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
            "consumes_qft_gr_minimal_model_obstruction_class_stabilization_packet_result_review"
        ]
        == RESULT_REVIEW_ID
    )
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_qft_gr_minimal_positive_conservation_witness_packet_defines_toy_bridge() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["strict_toy_assumptions_only"] is True
    assert packet["packet_preparation_only"] is True
    assert packet["positive_witness_packet_prepared"] is True
    assert packet["positive_witness_bridge_law_scope"] == POSITIVE_WITNESS_BRIDGE_LAW
    assert packet["strict_toy_bridge_component_count"] == 8
    assert {
        row["component"] for row in packet["strict_toy_bridge_components"]
    } == {
        "allowed_weak_test_class",
        "weak_pairing",
        "source_object",
        "divergence_pairing",
        "field_equation_residual",
        "divergence_identity",
        "compact_support_no_boundary_condition",
        "pass_fail_inconclusive_criteria",
    }
    assert all(
        row["required_for_bridge"] is True
        for row in packet["strict_toy_bridge_components"]
    )
    assert packet["allowed_weak_test_class_id"] == (
        "strict_toy_compact_support_smooth_test_vector_class_v0"
    )
    assert packet["weak_pairing_id"] == "strict_toy_source_test_pairing_v0"
    assert packet["source_object_id"] == "strict_toy_stress_energy_like_source_object_v0"
    assert packet["divergence_pairing_id"] == "strict_toy_weak_divergence_pairing_v0"
    assert packet["field_equation_residual_id"] == (
        "strict_toy_field_equation_residual_zero_v0"
    )
    assert packet["divergence_identity_id"] == (
        "strict_toy_divergence_identity_assumption_v0"
    )
    assert packet["no_boundary_condition_id"] == (
        "strict_toy_compact_support_no_boundary_condition_v0"
    )


def test_qft_gr_minimal_positive_conservation_witness_packet_sets_future_attempt_criteria() -> None:
    packet = _json(DEFAULT_OUT)
    criteria = packet["pass_fail_inconclusive_criteria"]
    assert set(criteria) == {"pass", "fail", "inconclusive"}
    assert "zero weak-divergence pairing" in criteria["pass"]
    assert "counterexample" in criteria["fail"]
    assert "insufficiently specified" in criteria["inconclusive"]
    assert packet["positive_witness_attempt_authorized_by_packet"] is False
    assert packet["positive_witness_attempt_executed"] is False
    assert packet["conservation_claimed"] is False
    assert packet["conservation_proved"] is False
    assert packet["conservation_witness_constructed"] is False


def test_qft_gr_minimal_positive_conservation_witness_packet_preserves_obstruction_and_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert packet["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert packet["dominant_obstruction_resolved"] is False
    assert packet["mathematical_resolution_claimed"] is False
    assert packet["immediate_retest_authorized"] is False
    assert packet["conservation_retest_rerun_authorized"] is False
    assert packet["ordinary_model_refinement_authorized"] is False
    assert packet["countermodel_lane_retained_as_follow_on"] is True
    assert packet["source_map_ladder_lane_retained_as_follow_on"] is True
    for key in [
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
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


def test_qft_gr_minimal_positive_conservation_witness_packet_selects_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_count"] == 1
    decisions = {row["target"]: row["decision"] for row in packet["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[ATTEMPT_TARGET] == "not_authorized_until_packet_review"
    assert decisions[
        "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement"
    ] == "not_authorized"
    assert decisions[
        "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_refinement"
    ] == "not_authorized"


def test_qft_gr_minimal_positive_conservation_witness_packet_updates_live_target() -> None:
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
        "QFTGRMinimalPositiveConservationWitnessPacketUnderStrictToyAssumptions.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    packet_workstream = _workstream(registry, CONSUMED_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["packet_prepared"] == "yes"
    assert packet_workstream["positive_witness_packet_prepared"] == "yes"
    assert packet_workstream["selected_next_target"] == NEXT_TARGET
    assert packet_workstream["positive_witness_attempt_executed"] == "no"
    assert packet_workstream["positive_witness_attempt_authorized_by_packet"] == "no"
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["conservation_witness_constructed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["result_review_pending"] == "yes"
    assert active_workstream["positive_witness_packet_prepared"] == "yes"
    assert active_workstream["positive_witness_attempt_executed"] == "no"
    assert active_workstream["positive_witness_attempt_authorized"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_qft_gr_minimal_positive_conservation_witness_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
    )
    assert generated == packet
    assert render_markdown(packet) == _read(DEFAULT_MARKDOWN_OUT)


def test_qft_gr_minimal_positive_conservation_witness_packet_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "execute_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction_result",
        "strict_toy_compact_support_smooth_test_vector_class_v0",
        "strict_toy_source_test_pairing_v0",
        "strict_toy_weak_divergence_pairing_v0",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_qft_gr_minimal_positive_conservation_witness_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_gate.py"
    )
