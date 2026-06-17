from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    REVIEW_ID as RESULT_REVIEW_ID,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_source_map_or_countermodel_scope_decision_packet_report import (
    CONSUMED_TARGET,
    COUNTERMODEL_SCOPE_DECISION_TARGET,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
    build_qft_gr_source_map_or_countermodel_scope_decision_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_source_map_or_countermodel_scope_decision_packet_report.py"
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


def test_source_map_or_countermodel_scope_decision_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_source_map_or_countermodel_scope_decision_packet_consumes_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["packet_decision"] == "prepared"
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["consumes_result_review_id"] == RESULT_REVIEW_ID
    assert review["schema_id"] == RESULT_REVIEW_SCHEMA_ID
    assert review["review_id"] == RESULT_REVIEW_ID
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_source_map_or_countermodel_scope_decision_packet_selects_source_map_ladder() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["packet_selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_count"] == 1
    assert packet["source_map_ladder_branch_selected"] is True
    assert packet["source_map_ladder_selected_by_default"] is True
    assert packet["source_map_ladder_packet_authorized"] is True
    assert packet["source_map_ladder_packet_prepared"] is False
    assert packet["source_map_ladder_packet_executed"] is False
    assert packet["source_map_ladder_target"] == SOURCE_MAP_LADDER_TARGET


def test_source_map_or_countermodel_scope_decision_packet_rejects_scope_refinement_loop() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["countermodel_scope_refinement_target"] == COUNTERMODEL_SCOPE_DECISION_TARGET
    assert packet["countermodel_scope_refinement_branch_selected"] is False
    assert packet["countermodel_scope_refinement_branch_rejected"] is True
    assert packet["further_scope_refinement_authorized"] is False
    assert packet["automatic_countermodel_loop_authorized"] is False
    assert packet["one_more_scope_refinement_cycle_authorized"] is False
    assert packet["source_map_route_forced"] is True
    assert packet["exactly_one_narrow_scope_condition_identified"] is False
    assert packet["decision_forcing_narrow_scope_condition_count"] == 0


def test_source_map_or_countermodel_scope_decision_packet_carries_probe_gaps() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["probe_evaluation_count"] == 5
    assert packet["not_decisive_probe_count"] == 5
    assert packet["decisive_countermodel_pressure_point_count"] == 0
    assert packet["not_found_supporting_probe_count"] == 0
    assert packet["probe_semantic_gap_count"] == 5
    assert len(packet["probe_semantic_gap_assessment"]) == 5
    assert all(
        row["decision_forcing_as_single_scope_refinement"] == "no"
        for row in packet["probe_semantic_gap_assessment"]
    )
    assert packet["pinned_source_test_pair_id"] == PINNED_SOURCE_TEST_PAIR_ID
    assert packet["pinned_weak_pairing_contract_id"] == PINNED_WEAK_PAIRING_CONTRACT_ID
    assert packet["pinned_evaluation_scope_id"] == PINNED_EVALUATION_SCOPE_ID


def test_source_map_or_countermodel_scope_decision_packet_candidate_targets() -> None:
    packet = _json(DEFAULT_OUT)
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        COUNTERMODEL_SCOPE_DECISION_TARGET: (
            "not_selected_no_exactly_one_narrow_scope_condition"
        ),
        "review_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result": (
            "historical_prior_target_already_consumed"
        ),
        "claim_countermodel_exists": "not_authorized",
        "claim_no_go_result": "not_authorized",
        "claim_countermodel_not_found": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_broad_qft_gr_conservation": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
        "promote_master_action": "not_authorized",
    }
    assert packet["branch_option_count"] == 2
    assert {
        row["branch_target"]: row["branch_status"] for row in packet["branch_options"]
    } == {
        SOURCE_MAP_LADDER_TARGET: "selected",
        COUNTERMODEL_SCOPE_DECISION_TARGET: "not_selected",
    }


def test_source_map_or_countermodel_scope_decision_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["strict_toy_witness_preserved"] is True
    assert packet["strict_toy_witness_accepted"] is True
    assert packet["strict_toy_assumptions_only"] is True
    assert packet["decision_packet_is_not_strict_toy_witness_refutation"] is True
    assert packet["dominant_obstruction_candidate"] == "weak_pairing_domain_obstruction"
    assert (
        packet["canonical_obstruction_id"]
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
    )
    assert packet["dominant_obstruction_resolved"] is False
    assert packet["mathematical_resolution_claimed"] is False
    for key in [
        "countermodel_result_claimed",
        "countermodel_exists_claimed",
        "countermodel_achieved",
        "no_go_result_claimed",
        "not_found_result_claimed",
        "not_found_under_pinned_scope_claimed",
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "conservation_claimed",
        "full_qft_gr_conservation_claimed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_claimed",
        "empirical_validation_claimed",
        "public_submission_authorized",
        "master_action_promoted",
        "master_action_promotion_authorized",
    ]:
        assert packet[key] is False, key


def test_source_map_or_countermodel_scope_decision_packet_validation_policy() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
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
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_source_map_or_countermodel_scope_decision_packet_updates_live_target() -> None:
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
        "QFTGRSourceMapOrCountermodelScopeDecisionPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    consumed_workstream = _workstream(registry, CONSUMED_TARGET)
    assert consumed_workstream["status"] == "paused"
    assert consumed_workstream["source_map_or_scope_decision_packet_prepared"] == "yes"
    assert consumed_workstream["source_map_ladder_branch_selected"] == "yes"
    assert consumed_workstream["further_scope_refinement_authorized"] == "no"
    assert consumed_workstream["countermodel_result_claimed"] == "no"
    assert consumed_workstream["no_go_result_claimed"] == "no"
    assert consumed_workstream["not_found_result_claimed"] == "no"
    assert consumed_workstream["source_admissibility_claimed"] == "no"
    assert consumed_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["authorized_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_classification"] == PACKET_CLASSIFICATION
    assert active_workstream["source_map_ladder_packet_authorized"] == "yes"
    assert active_workstream["source_map_ladder_packet_prepared"] == "no"
    assert active_workstream["countermodel_scope_refinement_branch_selected"] == "no"
    assert active_workstream["exactly_one_narrow_scope_condition_identified"] == "no"
    assert active_workstream["countermodel_result_claimed"] == "no"
    assert active_workstream["no_go_result_claimed"] == "no"
    assert active_workstream["not_found_result_claimed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_source_map_or_countermodel_scope_decision_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_source_map_or_countermodel_scope_decision_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-16T00:00:00Z",
    )
    assert generated == packet


def test_source_map_or_countermodel_scope_decision_packet_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
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
        COUNTERMODEL_SCOPE_DECISION_TARGET,
        PINNED_SOURCE_TEST_PAIR_ID,
        PINNED_WEAK_PAIRING_CONTRACT_ID,
        PINNED_EVALUATION_SCOPE_ID,
        "decisionPacketPrepared",
        "sourceMapLadderBranchSelected",
        "exactlyOneNarrowScopeConditionIdentified",
        "selectedSourceMapLadderPacketTarget",
        "consumedSourceMapOrCountermodelScopeDecisionPacketTarget",
        "no source admissibility",
        "no countermodel result",
        "no no-go result",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_source_map_or_countermodel_scope_decision_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_map_or_countermodel_scope_decision_packet_gate.py"
    )
