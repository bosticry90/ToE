from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet_report import (
    ACTION_DERIVABILITY_RESULT,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    SMOOTH_REFERENCE_FORM,
    TEST_SPACE,
    WEAK_VARIATIONAL_OBLIGATION,
    WELL_DEFINED_PAIRING_SCOPE,
    build_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet,
)
from formal.python.tools.qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet_report import (
    DEFAULT_OUT as WEAK_PAIRING_PACKET_PATH,
    OUTCOME_ID as WEAK_PAIRING_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
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
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_action_derivability_packet_files_exist() -> None:
    assert WEAK_PAIRING_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_action_derivability_packet_records_blocked_result() -> None:
    prior = _json(WEAK_PAIRING_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == WEAK_PAIRING_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert packet["action_derivability_constructed"] is False
    assert packet["source_is_action_derived"] is False
    assert packet["matter_action_functional_supplied"] is False
    assert packet["metric_variation_rule_supplied"] is False
    assert packet["variational_domain_for_action_supplied"] is False


def test_action_derivability_packet_binds_pairing_and_variational_obligation() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert packet["functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert packet["test_domain"] == TEST_SPACE
    assert packet["weak_pairing_scope"] == WELL_DEFINED_PAIRING_SCOPE
    assert packet["weak_pairing_constructed"] is True
    assert packet["weak_variational_obligation"] == WEAK_VARIATIONAL_OBLIGATION
    assert packet["smooth_reference_form"] == SMOOTH_REFERENCE_FORM
    assert packet["mathematical_statement"] == (
        "The pairable distributional tensor T would be action-derived only "
        "if a licensed matter action S_m supplied the weak variation "
        "delta S_m[g](h) = -1/2 T(h). The weak pairing alone does not "
        "supply S_m, so action derivability is blocked."
    )


def test_action_derivability_packet_records_missing_action_data() -> None:
    packet = _json(DEFAULT_OUT)
    obligations = {
        row["obligation_id"]: row for row in packet["action_derivability_obligations"]
    }
    assert list(obligations) == [
        "matter_action_functional",
        "metric_variation_rule",
        "variational_domain",
        "sign_and_normalization_convention",
        "covariance_or_diffeomorphism_behavior",
        "boundary_support_conditions",
    ]
    assert obligations["matter_action_functional"]["status"] == "missing"
    assert obligations["metric_variation_rule"]["required_form"] == (
        WEAK_VARIATIONAL_OBLIGATION
    )
    assert obligations["metric_variation_rule"]["status"] == "missing"
    assert obligations["variational_domain"]["required_form"] == f"h in {TEST_SPACE}"
    assert obligations["variational_domain"]["status"] == (
        "missing_for_action_functional"
    )
    for blocker in [
        "matter_action_functional",
        "metric_variation_rule",
        "variational_domain",
        "sign_and_normalization_convention",
    ]:
        assert blocker in packet["action_derivability_blockers"]


def test_action_derivability_packet_attempts_derivation_and_blocks_correctly() -> None:
    packet = _json(DEFAULT_OUT)
    steps = {row["step_id"]: row for row in packet["calculation_steps"]}
    assert list(steps) == [
        "bind_pairable_candidate",
        "state_weak_variational_obligation",
        "search_for_licensed_action_functional",
        "derive_action_variation",
    ]
    assert steps["bind_pairable_candidate"]["passed"] is True
    assert steps["state_weak_variational_obligation"]["statement"] == (
        WEAK_VARIATIONAL_OBLIGATION
    )
    assert steps["state_weak_variational_obligation"]["passed"] is True
    assert steps["search_for_licensed_action_functional"]["result"] == (
        "no_matter_action_functional_supplied"
    )
    assert steps["search_for_licensed_action_functional"]["passed"] is False
    assert steps["derive_action_variation"]["result"] == (
        "blocked_by_missing_action_functional"
    )
    assert steps["derive_action_variation"]["passed"] is False


def test_action_derivability_packet_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
        "weak_conservation_claimed",
        "conservation_claimed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "public_submission_authorized",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["weak_pairing"]["status"] == "COMPLETED_RESTRICTED"
    assert progression["action_derivability"]["status"] == "BLOCKED"
    assert progression["action_derivability"]["decision"] == ACTION_DERIVABILITY_RESULT
    assert progression["matter_action_functional_candidate"]["status"] == (
        "NEXT_TARGET_AUTHORIZED"
    )
    assert progression["matter_action_functional_candidate"]["decision"] == NEXT_TARGET
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert (
        build_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet()
        == packet
    )


def test_action_derivability_packet_updates_live_target_to_matter_action_packet() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRActionDerivabilityTestForDistributionalSymmetricTensorCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_ACTION_DERIVABILITY_TEST_FOR_DISTRIBUTIONAL_SYMMETRIC_"
        "TENSOR_CANDIDATE_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert consumed["matter_action_functional_supplied"] == "no"
    assert consumed["source_is_action_derived"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert active_row["matter_action_functional_supplied"] == "no"
    assert active_row["action_derivability_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_action_derivability_packet_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        SELECTED_REPLACEMENT_CANDIDATE_ID,
        ACTION_DERIVABILITY_RESULT,
        WEAK_VARIATIONAL_OBLIGATION,
        "QFTGRActionDerivabilityTestForDistributionalSymmetricTensorCandidatePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_matter_action_functional_candidate_packet",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_action_derivability_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet_gate.py"
    )
