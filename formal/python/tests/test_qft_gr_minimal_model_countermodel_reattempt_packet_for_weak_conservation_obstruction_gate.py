from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_report import (
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    NOT_FOUND_CLASSIFICATION,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_report import (
    CONSUMED_TARGET,
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
    build_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    REVIEW_ID as RESULT_REVIEW_ID,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_"
        "conservation_obstruction_report.py"
    )
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


def test_countermodel_reattempt_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_countermodel_reattempt_packet_consumes_refined_scope_review() -> None:
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
    assert packet["consumes_scope_refinement_attempt_result_review"] == RESULT_REVIEW_ID
    assert review["schema_id"] == RESULT_REVIEW_SCHEMA_ID
    assert review["review_id"] == RESULT_REVIEW_ID
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_countermodel_reattempt_packet_carries_refined_scope() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["countermodel_lane_decidability_scope_accepted"] is True
    assert packet["countermodel_reattempt_packet_prepared"] is True
    assert packet["countermodel_reattempt_packet_preparation_only"] is True
    assert packet["countermodel_reattempt_packet_result_review_pending"] is True
    assert packet["countermodel_reattempt_packet_result_reviewed"] is False
    assert packet["pinned_source_test_pair_id"] == PINNED_SOURCE_TEST_PAIR_ID
    assert packet["pinned_weak_pairing_contract_id"] == PINNED_WEAK_PAIRING_CONTRACT_ID
    assert packet["pinned_evaluation_scope_id"] == PINNED_EVALUATION_SCOPE_ID
    assert packet["source_test_instantiation"]["instantiation_id"] == PINNED_SOURCE_TEST_PAIR_ID
    assert packet["weak_pairing_semantics"]["partiality_pinned"] == "yes"
    assert packet["weak_pairing_semantics"]["totality_claimed"] == "no"
    assert packet["evaluation_scope"]["evaluation_scope_id"] == PINNED_EVALUATION_SCOPE_ID


def test_countermodel_reattempt_packet_prepares_five_probe_protocol() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["reattempt_probe_count"] == 5
    assert len(packet["reattempt_probe_plan"]) == 5
    assert packet["reattempt_decision_protocol"]["probe_count"] == 5
    assert packet["reattempt_decision_protocol"]["review_required_before_execution"] == "yes"
    assert packet["allowed_reattempt_classification_count"] == 3
    assert {
        row["classification"] for row in packet["allowed_reattempt_classifications"]
    } == {FOUND_CLASSIFICATION, NOT_FOUND_CLASSIFICATION, INCONCLUSIVE_CLASSIFICATION}
    assert all(
        row["selected_now"] == "no"
        for row in packet["allowed_reattempt_classifications"]
    )
    assert packet["found_classification_not_selected"] is True
    assert packet["not_found_classification_not_selected"] is True
    assert packet["inconclusive_classification_not_selected"] is True
    assert packet["selected_countermodel_criterion_count"] == 0
    assert packet["selected_no_go_criterion_count"] == 0


def test_countermodel_reattempt_packet_selects_result_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["packet_selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_count"] == 1
    assert packet["countermodel_reattempt_authorized_by_packet"] is False
    assert packet["countermodel_reattempt_executed"] is False
    assert {
        row["target"]: row["decision"] for row in packet["candidate_next_targets"]
    } == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction": (
            "not_authorized_until_reattempt_packet_result_review"
        ),
        "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source": (
            "retained_follow_on_not_selected_by_this_packet"
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


def test_countermodel_reattempt_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["strict_toy_witness_preserved"] is True
    assert packet["strict_toy_witness_accepted"] is True
    assert packet["strict_toy_assumptions_only"] is True
    assert packet["countermodel_reattempt_packet_is_not_strict_toy_witness_refutation"] is True
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
        "inconclusive_result_claimed",
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


def test_countermodel_reattempt_packet_validation_policy() -> None:
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


def test_countermodel_reattempt_packet_updates_live_target() -> None:
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
        "QFTGRMinimalModelCountermodelReattemptPacketForWeakConservationObstruction.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
        "CONSERVATION_OBSTRUCTION_20260615_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    consumed_workstream = _workstream(registry, CONSUMED_TARGET)
    assert consumed_workstream["status"] == "paused"
    assert consumed_workstream["countermodel_reattempt_packet_prepared"] == "yes"
    assert consumed_workstream["countermodel_reattempt_packet_result_review_pending"] == "yes"
    assert consumed_workstream["countermodel_reattempt_executed"] == "no"
    assert consumed_workstream["countermodel_result_claimed"] == "no"
    assert consumed_workstream["no_go_result_claimed"] == "no"
    assert consumed_workstream["source_admissibility_claimed"] == "no"
    assert consumed_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_classification"] == PACKET_CLASSIFICATION
    assert active_workstream["countermodel_reattempt_packet_prepared"] == "yes"
    assert active_workstream["countermodel_reattempt_packet_result_review_pending"] == "yes"
    assert active_workstream["countermodel_reattempt_packet_result_reviewed"] == "no"
    assert active_workstream["countermodel_reattempt_executed"] == "no"
    assert active_workstream["countermodel_result_claimed"] == "no"
    assert active_workstream["no_go_result_claimed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_countermodel_reattempt_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-15T00:00:00Z",
    )
    assert generated == packet


def test_countermodel_reattempt_packet_lean_and_surface_mirrors() -> None:
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
        PINNED_SOURCE_TEST_PAIR_ID,
        PINNED_WEAK_PAIRING_CONTRACT_ID,
        PINNED_EVALUATION_SCOPE_ID,
        "countermodelReattemptPacketPrepared",
        "reattemptProbeCount",
        "allowedReattemptClassificationCount",
        "no source admissibility",
        "no countermodel result",
        "no no-go result",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_countermodel_reattempt_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_gate.py"
    )
