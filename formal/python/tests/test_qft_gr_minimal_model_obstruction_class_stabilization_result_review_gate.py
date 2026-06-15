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
    DEFAULT_OUT as PACKET_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as PACKET_REVIEW_TARGET,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POSITIVE_WITNESS_TARGET,
    SCHEMA_ID as PACKET_SCHEMA_ID,
    STATUS as OBSTRUCTION_STATUS,
)
from formal.python.tools.qft_gr_minimal_model_obstruction_class_stabilization_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_minimal_model_obstruction_class_stabilization_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_model_obstruction_class_stabilization_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelObstructionClassStabilizationResultReview.lean"
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


def test_obstruction_class_stabilization_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_obstruction_class_stabilization_result_review_consumes_packet() -> None:
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
        review["consumes_qft_gr_minimal_model_obstruction_class_stabilization_packet"]
        == PACKET_ID
    )
    assert packet["schema_id"] == PACKET_SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == PACKET_REVIEW_TARGET
    assert CONSUMED_TARGET == PACKET_REVIEW_TARGET


def test_obstruction_class_stabilization_result_review_accepts_unresolved_candidate() -> None:
    review = _json(DEFAULT_OUT)
    assert review["packet_result_review_accepted"] is True
    assert (
        review["obstruction_class_stabilization_packet_result_review_accepted"]
        is True
    )
    assert review["obstruction_class_stabilization_packet_consumed"] is True
    assert review["decision_forcing_classification_step_accepted"] is True
    assert review["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert review["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert review["obstruction_status"] == OBSTRUCTION_STATUS
    assert review["dominant_obstruction_candidate_accepted"] is True
    assert review["dominant_obstruction_resolved"] is False
    assert review["mathematical_resolution_claimed"] is False
    assert review["obstruction_solved"] is False
    assert review["attempt_chain_count"] == 5
    assert review["latest_result_marked_inconclusive"] is True
    assert (
        review["repeated_inconclusive_pattern_accepted_as_stabilization_signal"]
        is True
    )
    assert review["supporting_obstruction_count"] == 7
    assert review["supporting_obstructions_retained_unresolved"] is True


def test_obstruction_class_stabilization_result_review_authorizes_positive_witness_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["positive_witness_packet_authorized"] is True
    assert review["positive_witness_packet_prepared_by_review"] is False
    assert review["positive_witness_attempt_authorized"] is False
    assert review["positive_witness_attempt_executed"] is False
    assert review["positive_witness_bridge_law_scope"] == POSITIVE_WITNESS_BRIDGE_LAW
    assert review["immediate_retest_authorized"] is False
    assert review["conservation_retest_rerun_authorized"] is False
    assert review["ordinary_model_refinement_authorized"] is False
    assert review["countermodel_lane_retained_as_follow_on"] is True
    assert review["countermodel_packet_authorized"] is False
    assert review["source_map_ladder_lane_retained_as_follow_on"] is True
    assert review["source_map_ladder_packet_authorized"] is False
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selected_next_target_count"] == 1
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]}[
        POSITIVE_WITNESS_TARGET
    ] == "selected"
    assert NEXT_TARGET == POSITIVE_WITNESS_TARGET


def test_obstruction_class_stabilization_result_review_preserves_nonclaims() -> None:
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
    assert "no source admissibility" in review["non_claim_boundary"]
    assert "no conservation witness" in review["non_claim_boundary"]
    assert "not as solved mathematics" in review["non_claim_boundary"]


def test_obstruction_class_stabilization_result_review_validation_policy() -> None:
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
    assert policy["release_index_path_not_freshly_lean_validated"] is True
    assert policy["aggregate_lean_not_run"] is True
    assert review["aggregate_lean_timeout_caveat_preserved"] is True
    assert "Full pytest" in review["validation_caveat"]
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_obstruction_class_stabilization_result_review_updates_live_target() -> None:
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
        "QFTGRMinimalModelObstructionClassStabilizationResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_REVIEW_"
        "20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    review_workstream = _workstream(registry, CONSUMED_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["result_review_accepted"] == "yes"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["dominant_obstruction_resolved"] == "no"
    assert review_workstream["immediate_retest_authorized"] == "no"
    assert review_workstream["ordinary_model_refinement_authorized"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_preparation_pending"] == "yes"
    assert active_workstream["positive_witness_packet_authorized"] == "yes"
    assert active_workstream["positive_witness_attempt_authorized"] == "no"
    assert active_workstream["immediate_retest_authorized"] == "no"
    assert active_workstream["ordinary_model_refinement_authorized"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_obstruction_class_stabilization_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_model_obstruction_class_stabilization_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
    )
    assert review == generated

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
        DOMINANT_OBSTRUCTION_CANDIDATE,
        CANONICAL_OBSTRUCTION_ID,
        "not as solved mathematics",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_obstruction_class_stabilization_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_obstruction_class_stabilization_result_review_gate.py"
    )
