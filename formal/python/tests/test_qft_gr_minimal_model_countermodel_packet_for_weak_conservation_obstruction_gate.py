from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_report import (
    CANONICAL_OBSTRUCTION_ID,
    CONSUMED_TARGET,
    COUNTERMODEL_ATTEMPT_TARGET,
    DEFAULT_MARKDOWN_OUT,
    DEFAULT_OUT,
    DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBSTRUCTION_STATUS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
    build_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction,
    render_markdown,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_maturation_result_review_report import (
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_report.py"
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


def test_countermodel_packet_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert DEFAULT_MARKDOWN_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_countermodel_packet_consumes_maturation_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    result_review = _json(DEFAULT_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["accepted"] is True
    assert packet["packet_prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["consumes_result_review_id"] == REVIEW_ID
    assert result_review["schema_id"] == RESULT_REVIEW_SCHEMA_ID
    assert result_review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert result_review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert result_review["selected_next_target"] == CONSUMED_TARGET


def test_countermodel_packet_preserves_strict_toy_witness_without_refuting_it() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["countermodel_packet_is_not_strict_toy_witness_refutation"] is True
    assert packet["strict_toy_witness_preserved"] is True
    assert packet["strict_toy_witness_accepted"] is True
    assert packet["strict_toy_scope_accepted"] is True
    assert packet["strict_toy_assumptions_only"] is True
    assert packet["accepted_bridge_is_local_only"] is True
    assert packet["local_conservation_bridge_witness_accepted"] is True
    assert packet["positive_witness_bridge_law_scope"] == POSITIVE_WITNESS_BRIDGE_LAW
    scopes = {row["scope_id"]: row["status"] for row in packet["countermodel_pressure_scope"]}
    assert scopes["strict_toy_witness_preservation"] == "preserved_not_refuted"
    assert scopes["broader_candidate_family_pressure"] == (
        "selected_for_countermodel_definition"
    )


def test_countermodel_packet_defines_countermodel_or_no_go_criteria() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["countermodel_or_no_go_criteria_count"] == 7
    criteria = {row["criterion_id"]: row for row in packet["countermodel_or_no_go_criteria"]}
    for criterion in [
        "candidate_pairing_domain_undefined",
        "allowed_test_exposes_nonzero_weak_divergence",
        "derivative_exchange_not_justified",
        "boundary_term_survives_without_compact_support",
        "divergence_identity_not_derivable",
        "test_vector_class_mismatch",
        "curvature_coupling_leaves_uncancelled_term",
    ]:
        assert criterion in criteria
        assert criteria[criterion]["would_count_if"]
    assert packet["attempt_classification_count"] == 3
    classifications = {row["classification"] for row in packet["attempt_classifications"]}
    assert (
        "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
        "achieved_pending_result_review"
    ) in classifications
    assert (
        "qft_gr_minimal_model_no_go_pressure_for_weak_conservation_obstruction_"
        "identified_pending_result_review"
    ) in classifications
    assert (
        "qft_gr_minimal_model_countermodel_attempt_inconclusive_requires_"
        "assumption_or_source_map_stabilization"
    ) in classifications


def test_countermodel_packet_selects_result_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_count"] == 1
    decisions = {row["target"]: row["decision"] for row in packet["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[CONSUMED_TARGET] == "completed_consumed_live_target"
    assert decisions[COUNTERMODEL_ATTEMPT_TARGET] == (
        "not_authorized_until_packet_review"
    )
    assert decisions[SOURCE_MAP_LADDER_TARGET] == "retained_follow_on_not_selected"
    assert decisions["execute_immediate_conservation_retest"] == "not_authorized"
    assert decisions["claim_qft_gr_source_admissibility"] == "not_authorized"
    assert decisions["close_qft_gr_seam"] == "not_authorized"


def test_countermodel_packet_preserves_obstruction_and_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert packet["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert packet["obstruction_status"] == OBSTRUCTION_STATUS
    assert packet["dominant_obstruction_resolved"] is False
    assert packet["mathematical_resolution_claimed"] is False
    for key in [
        "countermodel_attempt_authorized",
        "countermodel_attempt_executed",
        "countermodel_result_claimed",
        "countermodel_achieved",
        "no_go_result_claimed",
        "inconclusive_result_claimed",
        "source_map_ladder_packet_authorized",
        "immediate_retest_authorized",
        "conservation_retest_rerun_authorized",
        "ordinary_model_refinement_authorized",
        "source_admissibility_can_be_considered",
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


def test_countermodel_packet_validation_policy() -> None:
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


def test_countermodel_packet_updates_live_target() -> None:
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
        "QFTGRMinimalModelCountermodelPacketForWeakConservationObstruction.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    packet_workstream = _workstream(registry, CONSUMED_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["countermodel_packet_prepared"] == "yes"
    assert packet_workstream["countermodel_packet_preparation_pending"] == "no"
    assert packet_workstream["selected_next_target"] == NEXT_TARGET
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["packet_result_review_pending"] == "yes"
    assert active_workstream["countermodel_packet_prepared"] == "yes"
    assert active_workstream["countermodel_attempt_authorized"] == "no"
    assert active_workstream["countermodel_result_claimed"] == "no"
    assert active_workstream["strict_toy_witness_preserved"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_countermodel_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction(
            result_review_path=DEFAULT_RESULT_REVIEW_PATH,
            captured_at_utc="2026-06-14T00:00:00Z",
        )
    )
    assert generated == packet
    assert render_markdown(packet) == _read(DEFAULT_MARKDOWN_OUT)


def test_countermodel_packet_lean_and_surface_mirrors() -> None:
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
        "review_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction",
        "strictToyWitnessPreserved",
        "countermodelPacketIsNotStrictToyWitnessRefutation",
        "candidate_pairing_domain_undefined",
        "allowed_test_exposes_nonzero_weak_divergence",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_countermodel_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_gate.py"
    )
