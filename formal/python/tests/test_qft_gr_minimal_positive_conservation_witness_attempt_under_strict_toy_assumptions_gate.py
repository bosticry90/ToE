from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_report import (
    ASSUMPTION_STABILIZATION_TARGET,
    ATTEMPT_ID,
    CANONICAL_OBSTRUCTION_ID,
    CONSUMED_TARGET,
    COUNTERMODEL_TARGET,
    DEFAULT_OUT,
    DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    FAILED_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_ATTEMPT_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBSTRUCTION_STATUS,
    OUTCOME_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_report.py"
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


def test_qft_gr_minimal_positive_conservation_witness_attempt_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_qft_gr_minimal_positive_conservation_witness_attempt_consumes_review() -> None:
    attempt = _json(DEFAULT_OUT)
    result_review = _json(DEFAULT_RESULT_REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["executed"] is True
    assert attempt["accepted"] is True
    assert attempt["attempt_decision"] == "executed"
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["consumed_target"] == CONSUMED_TARGET
    assert result_review["selected_next_target"] == CONSUMED_TARGET
    assert result_review["positive_witness_attempt_authorized"] is True
    assert result_review["bounded_witness_attempt_authorized_only"] is True


def test_qft_gr_minimal_positive_conservation_witness_attempt_classification() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["classification_options"] == [
        RESULT_CLASSIFICATION,
        FAILED_CLASSIFICATION,
        INCONCLUSIVE_CLASSIFICATION,
    ]
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert attempt["selected_classification"] == RESULT_CLASSIFICATION
    assert attempt["result_classification_count"] == 1
    assert attempt["selected_classification_count"] == 1
    assert attempt["failed_classification_not_selected"] is True
    assert attempt["inconclusive_classification_not_selected"] is True


def test_qft_gr_minimal_positive_conservation_witness_attempt_lean_theorem_shape() -> None:
    attempt = _json(DEFAULT_OUT)
    lean_text = _read(LEAN_ATTEMPT_PATH)
    assert attempt["theorem_bearing_attempt"] is True
    assert attempt["strict_toy_weak_conservation_witness_achieved"] is True
    assert attempt["strict_toy_weak_conservation_theorem_constructed"] is True
    assert attempt["weak_conservation_against_allowed_tests_proved"] is True
    assert attempt["lean_contains_required_shape"] is True
    for marker in [
        "structure StrictToyConservationData",
        "def weakConservationAgainstAllowedTests",
        "theorem strict_toy_weak_conservation_witness",
        "divergenceIdentityImpliesWeakConservation",
        "fieldEquationResidualZero",
        "divergenceIdentityAvailable",
        "allowedWeakPairingAvailable",
        "compactSupportNoBoundary",
    ]:
        assert marker in lean_text
    assert attempt["lean_theorem_file"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions.lean"
    )


def test_qft_gr_minimal_positive_conservation_witness_attempt_scope() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["strict_toy_assumptions_only"] is True
    assert attempt["positive_witness_bridge_law_scope"] == POSITIVE_WITNESS_BRIDGE_LAW
    assert attempt["dominant_obstruction_candidate"] == DOMINANT_OBSTRUCTION_CANDIDATE
    assert attempt["canonical_obstruction_id"] == CANONICAL_OBSTRUCTION_ID
    assert attempt["obstruction_status"] == OBSTRUCTION_STATUS
    assert attempt["dominant_obstruction_resolved"] is False
    assert attempt["mathematical_resolution_claimed"] is False
    assert attempt["allowed_weak_test_class_id"] == (
        "strict_toy_compact_support_smooth_test_vector_class_v0"
    )
    assert attempt["weak_pairing_id"] == "strict_toy_source_test_pairing_v0"
    assert attempt["source_object_id"] == "strict_toy_stress_energy_like_source_object_v0"
    assert attempt["divergence_pairing_id"] == "strict_toy_weak_divergence_pairing_v0"
    assert attempt["field_equation_residual_id"] == (
        "strict_toy_field_equation_residual_zero_v0"
    )
    assert attempt["divergence_identity_id"] == (
        "strict_toy_divergence_identity_assumption_v0"
    )
    assert attempt["no_boundary_condition_id"] == (
        "strict_toy_compact_support_no_boundary_condition_v0"
    )


def test_qft_gr_minimal_positive_conservation_witness_attempt_selects_review_only() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["positive_witness_attempt_executed"] is True
    assert attempt["positive_witness_attempt_result_reviewed"] is False
    assert attempt["strict_toy_witness_attempt_result_review_pending"] is True
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["attempt_selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["selection_count"] == 1
    assert attempt["selected_next_target_count"] == 1
    decisions = {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]}
    assert decisions[NEXT_TARGET] == "selected"
    assert decisions[COUNTERMODEL_TARGET] == (
        "not_selected_unless_result_review_rejects_or_fails"
    )
    assert decisions[ASSUMPTION_STABILIZATION_TARGET] == (
        "not_selected_because_attempt_classified_achieved"
    )
    assert decisions["claim_qft_gr_source_admissibility"] == "not_authorized"
    assert decisions["close_qft_gr_seam"] == "not_authorized"
    assert decisions["promote_master_action"] == "not_authorized"


def test_qft_gr_minimal_positive_conservation_witness_attempt_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["countermodel_lane_retained_as_follow_on"] is True
    assert attempt["source_map_ladder_lane_retained_as_follow_on"] is True
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
        assert attempt[key] is False, key


def test_qft_gr_minimal_positive_conservation_witness_attempt_validation_policy() -> None:
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
    assert attempt["aggregate_lean_timeout_caveat_preserved"] is True
    assert "Full pytest" in attempt["validation_caveat"]
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_qft_gr_minimal_positive_conservation_witness_attempt_updates_live_target() -> None:
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
        "QFTGRMinimalPositiveConservationWitnessAttemptUnderStrictToyAssumptions.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_20260614_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    consumed_workstream = _workstream(registry, CONSUMED_TARGET)
    assert consumed_workstream["status"] == "paused"
    assert consumed_workstream["positive_witness_attempt_executed"] == "yes"
    assert consumed_workstream["strict_toy_weak_conservation_witness_achieved"] == "yes"
    assert consumed_workstream["strict_toy_weak_conservation_theorem_constructed"] == "yes"
    assert consumed_workstream["weak_conservation_against_allowed_tests_proved"] == "yes"
    assert consumed_workstream["selected_next_target"] == NEXT_TARGET
    assert consumed_workstream["source_admissibility_claimed"] == "no"
    assert consumed_workstream["conservation_witness_constructed"] == "no"
    assert consumed_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == NEXT_TARGET
    assert active_workstream["consumed_target"] == CONSUMED_TARGET
    assert active_workstream["outcome_id"] == OUTCOME_ID
    assert active_workstream["result_review_pending"] == "yes"
    assert active_workstream["positive_witness_attempt_executed"] == "yes"
    assert active_workstream["strict_toy_weak_conservation_witness_achieved"] == "yes"
    assert active_workstream["strict_toy_weak_conservation_theorem_constructed"] == "yes"
    assert active_workstream["weak_conservation_against_allowed_tests_proved"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_qft_gr_minimal_positive_conservation_witness_attempt_deterministic() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        lean_attempt_path=LEAN_ATTEMPT_PATH,
        captured_at_utc="2026-06-14T00:00:00Z",
    )
    assert generated == attempt


def test_qft_gr_minimal_positive_conservation_witness_attempt_lean_and_surface_mirrors() -> None:
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
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction",
        "strict_toy_weak_conservation_witness",
        "strict_toy_compact_support_smooth_test_vector_class_v0",
        "strict_toy_source_test_pairing_v0",
        "strict_toy_weak_divergence_pairing_v0",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_qft_gr_minimal_positive_conservation_witness_attempt_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_assumptions_gate.py"
    )
