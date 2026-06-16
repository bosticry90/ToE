from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_report import (
    ATTEMPT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_ATTEMPT_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NOT_FOUND_CLASSIFICATION,
    OUTCOME_ID,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_result_review_report import (
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
    / "qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_report.py"
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


def test_countermodel_attempt_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_countermodel_attempt_consumes_result_review() -> None:
    attempt = _json(DEFAULT_OUT)
    result_review = _json(RESULT_REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["executed"] is True
    assert attempt["accepted"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["consumed_target"] == CONSUMED_TARGET
    assert attempt["consumes_countermodel_packet_result_review"] == RESULT_REVIEW_ID
    assert result_review["schema_id"] == RESULT_REVIEW_SCHEMA_ID
    assert result_review["review_id"] == RESULT_REVIEW_ID
    assert result_review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert result_review["selected_next_target"] == CONSUMED_TARGET


def test_countermodel_attempt_selects_inconclusive_classification_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert RESULT_CLASSIFICATION == INCONCLUSIVE_CLASSIFICATION
    assert attempt["selected_classification"] == INCONCLUSIVE_CLASSIFICATION
    assert attempt["classification_options"] == [
        FOUND_CLASSIFICATION,
        NOT_FOUND_CLASSIFICATION,
        INCONCLUSIVE_CLASSIFICATION,
    ]
    selected = [
        row["classification"]
        for row in attempt["classification_rows"]
        if row["selected"] is True
    ]
    assert selected == [INCONCLUSIVE_CLASSIFICATION]
    assert attempt["found_classification_not_selected"] is True
    assert attempt["not_found_classification_not_selected"] is True
    assert attempt["countermodel_found_pending_result_review"] is False
    assert attempt["countermodel_not_found_requires_source_map_ladder"] is False
    assert attempt["countermodel_scope_refinement_required_pending_result_review"] is True


def test_countermodel_attempt_evaluates_criteria_without_claiming_result() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["countermodel_or_no_go_criteria_count"] == 7
    assert len(attempt["criteria_assessment"]) == 7
    assert attempt["selected_countermodel_criterion_count"] == 0
    assert attempt["selected_no_go_criterion_count"] == 0
    for row in attempt["criteria_assessment"]:
        assert row["selected_as_countermodel_or_no_go_result"] == "no"
    assert attempt["scope_refinement_requirement_count"] == 3
    for key in [
        "countermodel_result_claimed",
        "countermodel_exists_claimed",
        "countermodel_achieved",
        "no_go_result_claimed",
        "not_found_result_claimed",
        "inconclusive_result_claimed",
    ]:
        assert attempt[key] is False, key


def test_countermodel_attempt_preserves_strict_toy_witness_and_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["strict_toy_witness_preserved"] is True
    assert attempt["strict_toy_witness_accepted"] is True
    assert attempt["strict_toy_assumptions_only"] is True
    assert attempt["countermodel_attempt_is_not_strict_toy_witness_refutation"] is True
    assert attempt["dominant_obstruction_candidate"] == "weak_pairing_domain_obstruction"
    assert (
        attempt["canonical_obstruction_id"]
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
    )
    assert attempt["dominant_obstruction_resolved"] is False
    assert attempt["mathematical_resolution_claimed"] is False
    for key in [
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


def test_countermodel_attempt_validation_policy() -> None:
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


def test_countermodel_attempt_updates_live_target() -> None:
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
        "QFTGRMinimalModelCountermodelAttemptForWeakConservationObstruction.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_20260615_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    consumed_workstream = _workstream(registry, CONSUMED_TARGET)
    assert consumed_workstream["status"] == "paused"
    assert consumed_workstream["countermodel_attempt_executed"] == "yes"
    assert consumed_workstream["countermodel_attempt_result_review_pending"] == "yes"
    assert consumed_workstream["result_classification"] == RESULT_CLASSIFICATION
    assert consumed_workstream["countermodel_result_claimed"] == "no"
    assert consumed_workstream["no_go_result_claimed"] == "no"
    assert consumed_workstream["source_admissibility_claimed"] == "no"
    assert consumed_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["countermodel_attempt_executed"] == "yes"
    assert active_workstream["countermodel_attempt_result_review_pending"] == "yes"
    assert active_workstream["countermodel_attempt_result_reviewed"] == "no"
    assert active_workstream["result_classification"] == RESULT_CLASSIFICATION
    assert active_workstream["countermodel_scope_refinement_required_pending_result_review"] == "yes"
    assert active_workstream["countermodel_result_claimed"] == "no"
    assert active_workstream["no_go_result_claimed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_countermodel_attempt_deterministic() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-15T00:00:00Z",
    )
    assert generated == attempt


def test_countermodel_attempt_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        INCONCLUSIVE_CLASSIFICATION,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction",
        "countermodelAttemptExecuted",
        "countermodelScopeRefinementRequiredPendingResultReview",
        "no source admissibility",
        "no countermodel result",
        "no no-go result",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_countermodel_attempt_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_gate.py"
    )
