from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_report import (
    DEFAULT_OUT as ATTEMPT_PATH,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as ATTEMPT_CLASSIFICATION,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review_report import (
    ASSUMPTION_STABILIZATION_TARGET,
    CANONICAL_OBSTRUCTION_ID,
    CONSUMED_TARGET,
    COUNTERMODEL_TARGET,
    DEFAULT_OUT,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    LEAN_REVIEW_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBSTRUCTION_STATUS,
    OUTCOME_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
    build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review_report.py"
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


def test_strict_toy_witness_attempt_result_review_files_exist() -> None:
    assert ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_strict_toy_witness_attempt_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(ATTEMPT_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["consumed_attempt_outcome_id"] == ATTEMPT_OUTCOME
    assert review["consumed_attempt_classification"] == ATTEMPT_CLASSIFICATION
    assert attempt["selected_next_target"] == CONSUMED_TARGET


def test_strict_toy_witness_attempt_result_review_accepts_local_witness() -> None:
    review = _json(DEFAULT_OUT)
    assert review["strict_toy_witness_attempt_result_review_accepted"] is True
    assert review["strict_toy_witness_accepted"] is True
    assert review["local_conservation_bridge_witness_accepted"] is True
    assert review["local_conservation_bridge_witness_constructed"] is True
    assert review["strict_toy_weak_conservation_witness_achieved"] is True
    assert review["strict_toy_weak_conservation_theorem_constructed"] is True
    assert review["weak_conservation_against_allowed_tests_proved"] is True
    assert review["theorem_bearing_attempt"] is True
    assert review["theorem_bearing_result_review"] is True
    assert review["strict_toy_assumptions_only"] is True
    assert review["local_witness_scope"] == (
        "strict_toy_local_weak_conservation_bridge_witness_only"
    )
    assert review["positive_witness_bridge_law_scope"] == POSITIVE_WITNESS_BRIDGE_LAW


def test_strict_toy_witness_attempt_result_review_lean_confirms_theorem() -> None:
    review = _json(DEFAULT_OUT)
    lean_text = _read(LEAN_REVIEW_PATH)
    for marker in [
        "import ToeFormal.Derivation.QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions",
        "theorem strict_toy_witness_result_review_accepts_bridge_theorem",
        "strict_toy_weak_conservation_witness",
        "weakConservationAgainstAllowedTests",
        "selectedMinimalPositiveConservationWitnessMaturationPacketTarget",
    ]:
        assert marker in lean_text
    for theorem_name in review["lean_result_review_theorem_names"]:
        assert f"theorem {theorem_name}" in lean_text
    assert review["lean_result_review_file"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptionsResultReview.lean"
    )


def test_strict_toy_witness_attempt_result_review_authorizes_maturation_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["maturation_packet_authorized"] is True
    assert review["witness_maturation_packet_authorized_only"] is True
    assert review["maturation_packet_prepared"] is False
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selection_count"] == 1
    assert review["selected_next_target_count"] == 1
    decisions = {row["target"]: row["decision"] for row in review["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[COUNTERMODEL_TARGET] == (
        "retained_follow_on_not_authorized_by_this_review"
    )
    assert decisions[ASSUMPTION_STABILIZATION_TARGET] == (
        "subsumed_by_witness_maturation_packet_not_selected"
    )
    assert decisions[SOURCE_MAP_LADDER_TARGET] == (
        "retained_follow_on_after_maturation_or_countermodel_pressure"
    )
    assert decisions["claim_qft_gr_source_admissibility"] == "not_authorized"
    assert decisions["close_qft_gr_seam"] == "not_authorized"
    assert decisions["promote_master_action"] == "not_authorized"


def test_strict_toy_witness_attempt_result_review_preserves_boundaries() -> None:
    review = _json(DEFAULT_OUT)
    assert review["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert review["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert review["obstruction_status"] == OBSTRUCTION_STATUS
    assert review["dominant_obstruction_resolved"] is False
    assert review["mathematical_resolution_claimed"] is False
    for key in [
        "countermodel_packet_authorized",
        "assumption_stabilization_packet_authorized",
        "source_map_ladder_packet_authorized",
        "immediate_retest_authorized",
        "conservation_retest_rerun_authorized",
        "ordinary_model_refinement_authorized",
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
        "conservation_claimed",
        "conservation_proved",
        "conservation_proof_object_constructed",
        "conservation_witness_constructed",
        "full_qft_gr_conservation_claimed",
        "unbounded_conservation_proved",
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


def test_strict_toy_witness_attempt_result_review_validation_policy() -> None:
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


def test_strict_toy_witness_attempt_result_review_updates_live_target() -> None:
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
        "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptionsResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_RESULT_REVIEW_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    review_workstream = _workstream(registry, CONSUMED_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["result_review_accepted"] == "yes"
    assert review_workstream["strict_toy_witness_accepted"] == "yes"
    assert review_workstream["local_conservation_bridge_witness_accepted"] == "yes"
    assert review_workstream["maturation_packet_authorized"] == "yes"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_preparation_pending"] == "yes"
    assert active_workstream["maturation_packet_authorized"] == "yes"
    assert active_workstream["strict_toy_witness_accepted"] == "yes"
    assert active_workstream["local_conservation_bridge_witness_accepted"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_strict_toy_witness_attempt_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review(
        attempt_path=ATTEMPT_PATH,
        lean_review_path=LEAN_REVIEW_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
    )
    assert generated == review


def test_strict_toy_witness_attempt_result_review_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "execute_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction",
        "strict_toy_witness_result_review_accepts_bridge_theorem",
        "strict_toy_local_weak_conservation_bridge_witness_only",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_strict_toy_witness_attempt_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review_gate.py"
    )
