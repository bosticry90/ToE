from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_report import (
    ATTEMPT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_ATTEMPT_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
    OUTCOME_ID,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    build_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result_review_report import (
    DEFAULT_OUT as PACKET_REVIEW_PATH,
    OUTCOME_ID as PACKET_REVIEW_OUTCOME,
    REVIEW_ID as PACKET_REVIEW_ID,
    SCHEMA_ID as PACKET_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_"
        "weak_conservation_obstruction_report.py"
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


def test_countermodel_attempt_after_scope_refinement_files_exist() -> None:
    assert PACKET_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_countermodel_attempt_after_scope_refinement_consumes_packet_review() -> None:
    attempt = _json(DEFAULT_OUT)
    packet_review = _json(PACKET_REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["executed"] is True
    assert attempt["accepted"] is True
    assert attempt["attempt_decision"] == "executed"
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["consumed_target"] == CONSUMED_TARGET
    assert attempt["consumes_reattempt_packet_result_review"] == PACKET_REVIEW_ID
    assert packet_review["schema_id"] == PACKET_REVIEW_SCHEMA_ID
    assert packet_review["review_id"] == PACKET_REVIEW_ID
    assert packet_review["outcome_id"] == PACKET_REVIEW_OUTCOME
    assert packet_review["selected_next_target"] == CONSUMED_TARGET


def test_countermodel_attempt_after_scope_refinement_runs_five_probe_protocol() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["pinned_source_test_pair_id"] == PINNED_SOURCE_TEST_PAIR_ID
    assert attempt["pinned_weak_pairing_contract_id"] == PINNED_WEAK_PAIRING_CONTRACT_ID
    assert attempt["pinned_evaluation_scope_id"] == PINNED_EVALUATION_SCOPE_ID
    assert attempt["source_test_instantiation"]["instantiation_id"] == PINNED_SOURCE_TEST_PAIR_ID
    assert attempt["weak_pairing_semantics"]["partiality_pinned"] == "yes"
    assert attempt["weak_pairing_semantics"]["totality_claimed"] == "no"
    assert attempt["evaluation_scope"]["probe_count"] == 5
    assert attempt["probe_count"] == 5
    assert attempt["probe_evaluation_count"] == 5
    assert len(attempt["probe_evaluations"]) == 5
    assert {
        row["probe_id"] for row in attempt["probe_evaluations"]
    } == {
        "weak_divergence_pairing_definedness",
        "weak_divergence_pairing_value",
        "boundary_term_retention",
        "derivative_exchange_legitimacy",
        "curvature_coupling_residual",
    }
    for row in attempt["probe_evaluations"]:
        assert row["evaluation_status"] == "not_decisive"
        assert row["pressure_point_selected"] == "no"
        assert row["countermodel_pressure_point_constructed"] is False
        assert row["not_found_support_established"] is False
    assert attempt["decisive_countermodel_pressure_point_count"] == 0
    assert attempt["not_found_supporting_probe_count"] == 0


def test_countermodel_attempt_after_scope_refinement_selects_inconclusive_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert RESULT_CLASSIFICATION == INCONCLUSIVE_CLASSIFICATION
    assert attempt["selected_classification"] == INCONCLUSIVE_CLASSIFICATION
    assert attempt["selected_classification_count"] == 1
    assert attempt["classification_options"] == [
        FOUND_CLASSIFICATION,
        NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
        INCONCLUSIVE_CLASSIFICATION,
    ]
    selected = [
        row["classification"]
        for row in attempt["classification_rows"]
        if row["selected"] is True
    ]
    assert selected == [INCONCLUSIVE_CLASSIFICATION]
    assert attempt["found_classification_not_selected"] is True
    assert attempt["not_found_under_pinned_scope_classification_not_selected"] is True
    assert attempt["countermodel_found_pending_result_review"] is False
    assert (
        attempt["countermodel_not_found_under_pinned_scope_requires_source_map_ladder"]
        is False
    )
    assert attempt["countermodel_inconclusive_requires_source_map_or_scope_decision"] is True
    assert attempt["countermodel_not_found_means_under_pinned_scope_only"] is True


def test_countermodel_attempt_after_scope_refinement_selects_result_review_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["attempt_selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["selection_count"] == 1
    assert attempt["selected_next_target_count"] == 1
    assert {
        row["target"]: row["decision"] for row in attempt["candidate_next_targets"]
    } == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source": (
            "retained_follow_on_not_selected_before_result_review"
        ),
        "prepare_qft_gr_minimal_model_countermodel_scope_refinement_packet_after_reattempt_for_weak_conservation_obstruction": (
            "retained_possible_branch_not_selected_before_result_review"
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
    assert attempt["source_map_ladder_packet_authorized"] is False
    assert attempt["further_scope_refinement_authorized"] is False
    assert attempt["result_review_must_choose_source_map_or_single_scope_decision"] is True


def test_countermodel_attempt_after_scope_refinement_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["strict_toy_witness_preserved"] is True
    assert attempt["strict_toy_witness_accepted"] is True
    assert attempt["strict_toy_assumptions_only"] is True
    assert (
        attempt["attempt_after_scope_refinement_is_not_strict_toy_witness_refutation"]
        is True
    )
    assert attempt["dominant_obstruction_candidate"] == "weak_pairing_domain_obstruction"
    assert (
        attempt["canonical_obstruction_id"]
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
    )
    assert attempt["dominant_obstruction_resolved"] is False
    assert attempt["mathematical_resolution_claimed"] is False
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
        assert attempt[key] is False, key


def test_countermodel_attempt_after_scope_refinement_validation_policy() -> None:
    attempt = _json(DEFAULT_OUT)
    policy = attempt["validation_policy"]
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
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_countermodel_attempt_after_scope_refinement_updates_live_target() -> None:
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
        "QFTGRMinimalModelCountermodelAttemptAfterScopeRefinementForWeakConservationObstruction.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_"
        "WEAK_CONSERVATION_OBSTRUCTION_20260615_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    consumed_workstream = _workstream(registry, CONSUMED_TARGET)
    assert consumed_workstream["status"] == "paused"
    assert consumed_workstream["attempt_after_scope_refinement_executed"] == "yes"
    assert consumed_workstream["attempt_after_scope_refinement_result_review_pending"] == "yes"
    assert consumed_workstream["result_classification"] == RESULT_CLASSIFICATION
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
    assert active_workstream["result_classification"] == RESULT_CLASSIFICATION
    assert active_workstream["attempt_after_scope_refinement_executed"] == "yes"
    assert active_workstream["attempt_after_scope_refinement_result_review_pending"] == "yes"
    assert active_workstream["attempt_after_scope_refinement_result_reviewed"] == "no"
    assert active_workstream["countermodel_inconclusive_requires_source_map_or_scope_decision"] == "yes"
    assert active_workstream["countermodel_found_pending_result_review"] == "no"
    assert (
        active_workstream[
            "countermodel_not_found_under_pinned_scope_requires_source_map_ladder"
        ]
        == "no"
    )
    assert active_workstream["countermodel_result_claimed"] == "no"
    assert active_workstream["no_go_result_claimed"] == "no"
    assert active_workstream["not_found_result_claimed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_countermodel_attempt_after_scope_refinement_deterministic() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction(
        packet_review_path=PACKET_REVIEW_PATH,
        captured_at_utc="2026-06-15T00:00:00Z",
    )
    assert generated == attempt


def test_countermodel_attempt_after_scope_refinement_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_ATTEMPT_PATH,
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
        ATTEMPT_ID,
        OUTCOME_ID,
        RESULT_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        PINNED_SOURCE_TEST_PAIR_ID,
        PINNED_WEAK_PAIRING_CONTRACT_ID,
        PINNED_EVALUATION_SCOPE_ID,
        "attemptAfterScopeRefinementExecuted",
        "inconclusiveClassificationSelected",
        "resultReviewMustChooseSourceMapOrScopeDecision",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction",
        "no source admissibility",
        "no countermodel result",
        "no no-go result",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_countermodel_attempt_after_scope_refinement_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_gate.py"
    )
