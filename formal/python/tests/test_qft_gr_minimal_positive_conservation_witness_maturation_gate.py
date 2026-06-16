from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_maturation_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_MARKDOWN_OUT,
    DEFAULT_OUT,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    SCHEMA_ID,
    build_qft_gr_minimal_positive_conservation_witness_maturation_packet,
    render_markdown,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_positive_conservation_witness_maturation_report.py"
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


def test_positive_conservation_witness_maturation_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert DEFAULT_MARKDOWN_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_positive_conservation_witness_maturation_consumes_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    result_review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["packet_prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["consumed_result_review_outcome_id"] == RESULT_REVIEW_OUTCOME
    assert packet["consumed_result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert result_review["selected_next_target"] == CONSUMED_TARGET


def test_positive_conservation_witness_maturation_records_local_witness_scope() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["strict_toy_witness_accepted"] is True
    assert packet["local_conservation_bridge_witness_accepted"] is True
    assert packet["local_conservation_bridge_witness_constructed"] is True
    assert packet["strict_toy_weak_conservation_witness_achieved"] is True
    assert packet["strict_toy_weak_conservation_theorem_constructed"] is True
    assert packet["weak_conservation_against_allowed_tests_proved"] is True
    assert packet["strict_toy_assumptions_only"] is True
    assert packet["local_witness_scope"] == (
        "strict_toy_local_weak_conservation_bridge_witness_only"
    )
    assert packet["positive_witness_bridge_law_scope"] == POSITIVE_WITNESS_BRIDGE_LAW
    assert {row["claim_id"] for row in packet["witness_proves"]} == {
        "strict_toy_local_weak_conservation_bridge_witness",
        "theorem_shape_confirmed",
    }


def test_positive_conservation_witness_maturation_lists_assumption_burdens() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["strict_toy_assumption_count"] == 7
    assert packet["supplied_not_derived_count"] == 6
    assert packet["source_admissibility_precondition_count"] == 7
    assert {row["item"] for row in packet["supplied_not_derived"]} == {
        "divergence_identity",
        "residual_zero_to_real_field_equation_link",
        "allowed_weak_pairing_domain",
        "compact_support_no_boundary_condition",
        "source_object_physical_admissibility",
        "Bianchi_compatibility",
    }
    assert all(
        row["status"].startswith("not_yet_satisfied")
        for row in packet["source_admissibility_preconditions_before_consideration"]
    )
    assert packet["source_admissibility_can_be_considered"] is False


def test_positive_conservation_witness_maturation_preserves_obstruction_candidate() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert packet["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert packet["obstruction_status"] == "stabilized_for_next_target_selection_not_resolved"
    assert packet["dominant_obstruction_resolved"] is False
    assert packet["mathematical_resolution_claimed"] is False


def test_positive_conservation_witness_maturation_authorizes_result_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_count"] == 1
    decisions = {row["target"]: row["decision"] for row in packet["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[CONSUMED_TARGET] == "completed_consumed_live_target"
    assert decisions["execute_qft_gr_minimal_positive_conservation_witness_maturation_attempt"] == (
        "not_authorized_until_packet_review"
    )
    assert decisions[
        "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction"
    ] == "retained_follow_on_not_selected"
    assert decisions[
        "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source"
    ] == "retained_follow_on_not_selected"
    assert decisions["claim_qft_gr_source_admissibility"] == "not_authorized"
    assert decisions["close_qft_gr_seam"] == "not_authorized"
    assert decisions["promote_master_action"] == "not_authorized"


def test_positive_conservation_witness_maturation_preserves_boundaries() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "maturation_attempt_authorized",
        "countermodel_packet_authorized",
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
        assert packet[key] is False, key


def test_positive_conservation_witness_maturation_validation_policy() -> None:
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
    assert packet["aggregate_lean_timeout_caveat_preserved"] is True
    assert "Full pytest" in packet["validation_caveat"]
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_positive_conservation_witness_maturation_updates_live_target() -> None:
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
        "QFTGRMinimalPositiveConservationWitnessMaturation.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_MATURATION_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    packet_workstream = _workstream(registry, CONSUMED_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["maturation_packet_prepared"] == "yes"
    assert packet_workstream["source_admissibility_can_be_considered"] == "no"
    assert packet_workstream["selected_next_target"] == NEXT_TARGET
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_result_review_pending"] == "yes"
    assert active_workstream["maturation_packet_prepared"] == "yes"
    assert active_workstream["maturation_packet_result_reviewed"] == "no"
    assert active_workstream["source_admissibility_can_be_considered"] == "no"
    assert active_workstream["strict_toy_witness_accepted"] == "yes"
    assert active_workstream["local_conservation_bridge_witness_accepted"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_positive_conservation_witness_maturation_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_positive_conservation_witness_maturation_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
    )
    assert generated == packet
    assert render_markdown(packet) == _read(DEFAULT_MARKDOWN_OUT)


def test_positive_conservation_witness_maturation_lean_and_surface_mirrors() -> None:
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
        "review_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction",
        "suppliedRatherThanDerivedCore",
        "sourceAdmissibilityStillForbidden",
        "strict_toy_local_weak_conservation_bridge_witness_only",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_positive_conservation_witness_maturation_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_positive_conservation_witness_maturation_gate.py"
    )
