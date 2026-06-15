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
    DEFAULT_OUT as ATTEMPT_PATH,
    INCONCLUSIVE_CLASSIFICATION,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    SCHEMA_ID as ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_REVIEW_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
        "obstruction_result_review_report.py"
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


def test_countermodel_attempt_result_review_files_exist() -> None:
    assert ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_countermodel_attempt_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(ATTEMPT_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["consumes_countermodel_attempt_id"] == ATTEMPT_ID
    assert attempt["schema_id"] == ATTEMPT_SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["outcome_id"] == ATTEMPT_OUTCOME
    assert attempt["result_classification"] == INCONCLUSIVE_CLASSIFICATION
    assert attempt["selected_next_target"] == CONSUMED_TARGET


def test_countermodel_attempt_result_review_accepts_inconclusive_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["countermodel_attempt_result_review_accepted"] is True
    assert review["countermodel_attempt_result_reviewed"] is True
    assert review["inconclusive_countermodel_attempt_accepted"] is True
    assert review["result_classification"] == INCONCLUSIVE_CLASSIFICATION
    assert review["selected_classification"] == INCONCLUSIVE_CLASSIFICATION
    assert review["found_classification_not_selected"] is True
    assert review["not_found_classification_not_selected"] is True
    assert review["countermodel_found_pending_result_review"] is False
    assert review["countermodel_not_found_requires_source_map_ladder"] is False
    for key in [
        "countermodel_result_claimed",
        "countermodel_exists_claimed",
        "countermodel_achieved",
        "no_go_result_claimed",
        "not_found_result_claimed",
        "inconclusive_result_claimed",
    ]:
        assert review[key] is False, key


def test_countermodel_attempt_result_review_authorizes_scope_refinement_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selected_next_target_count"] == 1
    assert review["selection_count"] == 1
    assert review["countermodel_scope_refinement_required"] is True
    assert review["countermodel_scope_refinement_packet_authorized"] is True
    assert review["countermodel_scope_refinement_packet_authorized_only"] is True
    assert review["countermodel_scope_refinement_packet_prepared"] is False
    assert review["countermodel_scope_refinement_packet_executed"] is False
    assert review["scope_refinement_packet_preparation_pending"] is True
    assert review["scope_refinement_requirement_count"] == 3
    assert {
        row["target"]: row["decision"] for row in review["candidate_next_targets"]
    } == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source": (
            "retained_follow_on_not_selected_by_this_review"
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


def test_countermodel_attempt_result_review_preserves_strict_toy_witness_and_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["strict_toy_witness_preserved"] is True
    assert review["strict_toy_witness_accepted"] is True
    assert review["strict_toy_assumptions_only"] is True
    assert review["countermodel_attempt_is_not_strict_toy_witness_refutation"] is True
    assert review["dominant_obstruction_candidate"] == "weak_pairing_domain_obstruction"
    assert (
        review["canonical_obstruction_id"]
        == "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
    )
    assert review["dominant_obstruction_resolved"] is False
    assert review["mathematical_resolution_claimed"] is False
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
        assert review[key] is False, key


def test_countermodel_attempt_result_review_validation_policy() -> None:
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
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_countermodel_attempt_result_review_updates_live_target() -> None:
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
        "QFTGRMinimalModelCountermodelAttemptForWeakConservationObstructionResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_RESULT_REVIEW_20260615_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in state["completed_targets"]
    assert CONSUMED_TARGET in state["paused_lanes"]

    review_workstream = _workstream(registry, CONSUMED_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["countermodel_attempt_result_review_accepted"] == "yes"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["countermodel_scope_refinement_packet_authorized"] == "yes"
    assert review_workstream["countermodel_result_claimed"] == "no"
    assert review_workstream["no_go_result_claimed"] == "no"
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["countermodel_attempt_result_review_accepted"] == "yes"
    assert active_workstream["countermodel_attempt_result_reviewed"] == "yes"
    assert active_workstream["countermodel_scope_refinement_packet_authorized"] == "yes"
    assert active_workstream["countermodel_scope_refinement_packet_authorized_only"] == "yes"
    assert active_workstream["scope_refinement_packet_preparation_pending"] == "yes"
    assert active_workstream["countermodel_scope_refinement_packet_prepared"] == "no"
    assert active_workstream["result_classification"] == INCONCLUSIVE_CLASSIFICATION
    assert active_workstream["countermodel_result_claimed"] == "no"
    assert active_workstream["no_go_result_claimed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_countermodel_attempt_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review(
        attempt_path=ATTEMPT_PATH,
        captured_at_utc="2026-06-15T00:00:00Z",
    )
    assert generated == review


def test_countermodel_attempt_result_review_lean_and_surface_mirrors() -> None:
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
        INCONCLUSIVE_CLASSIFICATION,
        "countermodelAttemptResultReviewAccepted",
        "countermodelScopeRefinementPacketAuthorizedOnly",
        "no source admissibility",
        "no countermodel result",
        "no no-go result",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_countermodel_attempt_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review_gate.py"
    )
