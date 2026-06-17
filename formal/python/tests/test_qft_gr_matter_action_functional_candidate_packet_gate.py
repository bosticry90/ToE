from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet_report import (
    DEFAULT_OUT as ACTION_DERIVABILITY_PACKET_PATH,
    OUTCOME_ID as ACTION_DERIVABILITY_OUTCOME,
)
from formal.python.tools.qft_gr_matter_action_functional_candidate_packet_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EFFECTIVE_ACTION_FORM,
    FORMAL_VARIATIONAL_PRIMITIVE_FORM,
    LEAN_PACKET_PATH,
    MATTER_ACTION_RESULT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    TRUE_MATTER_ACTION_FORM,
    WEAK_VARIATIONAL_OBLIGATION,
    build_qft_gr_matter_action_functional_candidate_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_matter_action_functional_candidate_packet_report.py"
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


def test_matter_action_packet_files_exist() -> None:
    assert ACTION_DERIVABILITY_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_matter_action_packet_records_blocked_result() -> None:
    prior = _json(ACTION_DERIVABILITY_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == ACTION_DERIVABILITY_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["matter_action_result"] == MATTER_ACTION_RESULT
    assert packet["candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert packet["functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert packet["weak_variational_obligation"] == WEAK_VARIATIONAL_OBLIGATION
    assert packet["matter_action_functional_candidate_selected"] is False
    assert packet["action_derivability_retry_authorized"] is False
    assert packet["field_content_and_lagrangian_packet_required"] is True


def test_matter_action_packet_evaluates_three_routes_without_shortcut() -> None:
    packet = _json(DEFAULT_OUT)
    routes = {row["route_id"]: row for row in packet["route_assessments"]}
    assert list(routes) == [
        "true_matter_action_route",
        "effective_qft_action_route",
        "formal_variational_primitive_route",
    ]
    true_route = routes["true_matter_action_route"]
    assert true_route["candidate_form"] == TRUE_MATTER_ACTION_FORM
    assert true_route["required_variation"] == WEAK_VARIATIONAL_OBLIGATION
    assert true_route["selection_status"] == "blocked_not_selected"
    assert true_route["selection_licensed"] is False
    for blocker in [
        "matter_field_content_not_supplied",
        "lagrangian_density_not_supplied",
        "field_variation_policy_not_supplied",
        "metric_variation_rule_not_supplied",
        "variational_domain_not_supplied",
    ]:
        assert blocker in true_route["blocked_by"]

    effective_route = routes["effective_qft_action_route"]
    assert effective_route["candidate_form"] == EFFECTIVE_ACTION_FORM
    assert effective_route["selection_status"] == "recorded_not_licensed"
    assert effective_route["selection_licensed"] is False
    for blocker in [
        "qft_state_data_not_supplied",
        "renormalization_prescription_not_supplied",
        "effective_action_domain_not_supplied",
        "anomaly_handling_not_supplied",
    ]:
        assert blocker in effective_route["blocked_by"]

    formal_route = routes["formal_variational_primitive_route"]
    assert formal_route["candidate_form"] == FORMAL_VARIATIONAL_PRIMITIVE_FORM
    assert formal_route["selection_status"] == "recorded_not_selected"
    assert formal_route["selection_licensed"] is False
    assert formal_route["matter_action_admissibility_claimed"] is False
    assert "non_dynamical_primitive_not_matter_action" in formal_route["blocked_by"]


def test_matter_action_packet_records_missing_field_content_and_lagrangian() -> None:
    packet = _json(DEFAULT_OUT)
    required = {row["field_id"]: row for row in packet["required_action_data"]}
    assert required["matter_field_content"]["status"] == "missing"
    assert required["lagrangian_density"]["status"] == "missing"
    assert required["metric_variation_rule"]["required"] == WEAK_VARIATIONAL_OBLIGATION
    assert required["metric_variation_rule"]["status"] == "missing"
    assert required["variational_domain"]["status"] == "missing"
    assert required["sign_and_normalization_convention"]["status"] == (
        "target_convention_stated_not_derived"
    )
    assert required["distributional_compatibility"]["status"] == "not_reached"
    assert required["covariance_or_diffeomorphism_behavior"]["status"] == "not_reached"
    for missing in [
        "matter_field_content",
        "lagrangian_density",
        "metric_variation_rule",
        "variational_domain",
        "sign_and_normalization_convention",
    ]:
        assert missing in packet["missing_action_data"]
    assert packet["mathematical_statement"] == (
        "A true matter action route would require S_m[g, psi] with "
        "field content psi and Lagrangian density L_m such that "
        "delta S_m[g, psi](h) = -1/2 <T, h>. The current pairable "
        "distributional tensor supplies T but not psi, L_m, or a licensed "
        "metric-variation rule, so no matter action functional candidate "
        "is selected."
    )


def test_matter_action_packet_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["true_matter_action_route_selected"] is False
    assert packet["effective_qft_action_route_selected"] is False
    assert packet["formal_variational_primitive_selected"] is False
    assert packet["formal_variational_primitive_constructed"] is False
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
        "matter_action_admissibility_claimed",
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
    assert progression["matter_action_functional_candidate"]["status"] == "BLOCKED"
    assert progression["matter_action_functional_candidate"]["decision"] == (
        MATTER_ACTION_RESULT
    )
    assert progression["action_derivability_retry"]["status"] == "NOT_AUTHORIZED"
    assert progression["matter_field_content_and_lagrangian_candidate"][
        "status"
    ] == "NEXT_TARGET_AUTHORIZED"
    assert progression["matter_field_content_and_lagrangian_candidate"][
        "decision"
    ] == NEXT_TARGET
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert build_qft_gr_matter_action_functional_candidate_packet() == packet


def test_matter_action_packet_updates_live_target_to_field_content_packet() -> None:
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
        "QFTGRMatterActionFunctionalCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["matter_action_result"] == MATTER_ACTION_RESULT
    assert consumed["matter_action_functional_candidate_selected"] == "no"
    assert consumed["action_derivability_retry_authorized"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["matter_action_result"] == MATTER_ACTION_RESULT
    assert active_row["matter_field_content_supplied"] == "no"
    assert active_row["lagrangian_density_supplied"] == "no"
    assert active_row["action_derivability_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_matter_action_packet_lean_and_surface_mirrors() -> None:
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
        MATTER_ACTION_RESULT,
        TRUE_MATTER_ACTION_FORM,
        EFFECTIVE_ACTION_FORM,
        FORMAL_VARIATIONAL_PRIMITIVE_FORM,
        "QFTGRMatterActionFunctionalCandidatePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_matter_field_content_and_lagrangian_candidate_packet",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_matter_action_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_matter_action_functional_candidate_packet_gate.py"
    )
