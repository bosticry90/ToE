from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_report import (
    CANDIDATE_SOURCE_ID,
    CONSUMED_TARGET,
    DEFAULT_DECISION_PACKET_PATH,
    DEFAULT_OUT,
    FIRST_LADDER_BREAK_ROW_ID,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NON_PROMOTION_RESULT,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    SCHEMA_ID,
    build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source,
)
from formal.python.tools.qft_gr_source_map_or_countermodel_scope_decision_packet_report import (
    OUTCOME_ID as DECISION_PACKET_OUTCOME,
    PACKET_ID as DECISION_PACKET_ID,
    SCHEMA_ID as DECISION_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_report.py"
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


def test_source_map_ladder_packet_files_exist() -> None:
    assert DEFAULT_DECISION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_source_map_ladder_packet_consumes_decision_packet() -> None:
    packet = _json(DEFAULT_OUT)
    decision = _json(DEFAULT_DECISION_PACKET_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["packet_decision"] == "prepared"
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert decision["schema_id"] == DECISION_PACKET_SCHEMA_ID
    assert decision["packet_id"] == DECISION_PACKET_ID
    assert decision["outcome_id"] == DECISION_PACKET_OUTCOME
    assert decision["selected_next_target"] == CONSUMED_TARGET


def test_source_map_ladder_packet_identifies_candidate_only_source() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_source_object_id"] == CANDIDATE_SOURCE_ID
    assert packet["candidate_source_object_identified"] is True
    assert packet["candidate_source_object_supplied"] is True
    assert packet["candidate_source_is_admissible_source"] is False
    assert packet["source_admissibility_claimed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["physical_source_claimed"] is False


def test_source_map_ladder_packet_enumerates_ladder_and_first_break() -> None:
    packet = _json(DEFAULT_OUT)
    rows = packet["admissibility_ladder"]
    assert packet["admissibility_ladder_row_count"] == 12
    assert packet["admissibility_ladder_status_counts"] == {
        "absent": 5,
        "blocked": 2,
        "countermodel-sensitive": 3,
        "derivable": 0,
        "supplied": 2,
    }
    assert {row["status"] for row in rows} == {
        "supplied",
        "blocked",
        "absent",
        "countermodel-sensitive",
    }
    assert rows[2]["row_id"] == FIRST_LADDER_BREAK_ROW_ID
    assert rows[2]["status"] == "blocked"
    assert packet["first_ladder_break_row_id"] == FIRST_LADDER_BREAK_ROW_ID
    assert packet["first_ladder_break_status"] == "blocked"
    assert packet["ladder_break_identified"] is True


def test_source_map_ladder_packet_denies_current_admissibility_path() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["admissibility_path_exists_under_current_packet"] is False
    assert packet["legitimate_admissibility_path_exists"] is False
    assert packet["promotion_gate_satisfied"] is False
    assert packet["promotion_authorized"] is False
    assert packet["admissible_source_promotion_authorized"] is False
    assert packet["non_promotion_result"] == NON_PROMOTION_RESULT
    gate = packet["promotion_gate"]
    assert gate["promotion_authorized_by_this_packet"] is False
    assert gate["requires_result_review_acceptance_before_promotion"] is True
    assert gate["forbidden_current_statuses_for_promotion"] == [
        "blocked",
        "absent",
        "countermodel-sensitive",
    ]


def test_source_map_ladder_packet_preserves_countermodel_hooks() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["countermodel_hook_count"] == 5
    assert len(packet["countermodel_hooks"]) == 5
    assert {
        hook["probe_id"] for hook in packet["countermodel_hooks"]
    } == {
        "weak_divergence_pairing_definedness",
        "weak_divergence_pairing_value",
        "boundary_term_retention",
        "derivative_exchange_legitimacy",
        "curvature_coupling_residual",
    }
    assert all(
        hook["hook_status"] == "preserved_not_promoted"
        and hook["countermodel_result_claimed"] == "no"
        and hook["not_found_support_claimed"] == "no"
        for hook in packet["countermodel_hooks"]
    )


def test_source_map_ladder_packet_pinned_scope_and_obstruction() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["pinned_source_test_pair_id"] == PINNED_SOURCE_TEST_PAIR_ID
    assert packet["pinned_weak_pairing_contract_id"] == PINNED_WEAK_PAIRING_CONTRACT_ID
    assert packet["pinned_evaluation_scope_id"] == PINNED_EVALUATION_SCOPE_ID
    assert packet["strict_toy_witness_preserved"] is True
    assert packet["strict_toy_witness_accepted"] is True
    assert packet["dominant_obstruction_candidate"] == "weak_pairing_domain_obstruction"
    assert (
        packet["canonical_obstruction_id"]
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
    )
    assert packet["dominant_obstruction_resolved"] is False


def test_source_map_ladder_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "countermodel_result_claimed",
        "countermodel_exists_claimed",
        "countermodel_achieved",
        "no_go_result_claimed",
        "not_found_result_claimed",
        "not_found_under_pinned_scope_claimed",
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
        "expectation_value_source_claimed",
        "renormalized_stress_energy_object_claimed",
        "renormalization_closure_claimed",
        "conservation_claimed",
        "conservation_proved",
        "conservation_proof_object_constructed",
        "conservation_witness_constructed",
        "full_qft_gr_conservation_claimed",
        "unbounded_conservation_proved",
        "covariance_claimed",
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


def test_source_map_ladder_packet_validation_policy() -> None:
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


def test_source_map_ladder_packet_updates_live_target() -> None:
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
        "QFTGRSourceMapLadderPacketFromCandidateSourceToAdmissibleSource.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_"
        "ADMISSIBLE_SOURCE_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]

    consumed_workstream = _workstream(registry, CONSUMED_TARGET)
    assert consumed_workstream["status"] == "paused"
    assert consumed_workstream["source_map_ladder_packet_prepared"] == "yes"
    assert consumed_workstream["source_map_ladder_packet_result_review_pending"] == "yes"
    assert consumed_workstream["source_admissibility_claimed"] == "no"
    assert consumed_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["authorized_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_classification"] == PACKET_CLASSIFICATION
    assert active_workstream["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert active_workstream["source_map_ladder_packet_prepared"] == "yes"
    assert active_workstream["source_map_ladder_packet_result_review_pending"] == "yes"
    assert active_workstream["candidate_source_object_id"] == CANDIDATE_SOURCE_ID
    assert active_workstream["candidate_source_is_admissible_source"] == "no"
    assert active_workstream["first_ladder_break_row_id"] == FIRST_LADDER_BREAK_ROW_ID
    assert active_workstream["admissibility_path_exists_under_current_packet"] == "no"
    assert active_workstream["promotion_authorized"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_seam_closed"] == "no"


def test_source_map_ladder_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source(
            decision_packet_path=DEFAULT_DECISION_PACKET_PATH,
            captured_at_utc="2026-06-16T00:00:00Z",
        )
    )
    assert generated == packet


def test_source_map_ladder_packet_lean_and_surface_mirrors() -> None:
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
        CANDIDATE_SOURCE_ID,
        FIRST_LADDER_BREAK_ROW_ID,
        "sourceMapLadderPacketPrepared",
        "candidateSourceObjectIdentified",
        "admissibilityPathExistsUnderCurrentPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
        "admissible_source_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
        "admissible_source",
        "MASTER_ACTION_CURRENT_CITATION_TARGET_v0: "
        "review_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
        "admissible_source_result",
        "no source admissibility",
        "no countermodel result",
        "no no-go result",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_source_map_ladder_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_gate.py"
    )
