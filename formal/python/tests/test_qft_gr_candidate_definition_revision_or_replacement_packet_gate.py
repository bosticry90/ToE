from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet_report import (
    DEFAULT_OUT as REGULAR_TYPE_DOMAIN_PACKET_PATH,
    OUTCOME_ID as REGULAR_TYPE_DOMAIN_OUTCOME,
)
from formal.python.tools.qft_gr_candidate_definition_revision_or_replacement_packet_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DECISION_RESULT,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REQUIRED_FUNCTIONAL_CONTRACT,
    RETIRED_CANDIDATE_ID,
    SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_INDEX_PLACEMENT,
    SELECTED_PAIRING_RULE,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    SELECTED_REPLACEMENT_CANDIDATE_KIND,
    SELECTED_TENSOR_TYPE,
    TEST_SPACE,
    build_qft_gr_candidate_definition_revision_or_replacement_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_candidate_definition_revision_or_replacement_packet_report.py"
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


def test_candidate_definition_packet_files_exist() -> None:
    assert REGULAR_TYPE_DOMAIN_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_candidate_definition_packet_selects_replacement_candidate() -> None:
    prior = _json(REGULAR_TYPE_DOMAIN_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == REGULAR_TYPE_DOMAIN_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["decision_result"] == DECISION_RESULT
    assert packet["retired_candidate_id"] == RETIRED_CANDIDATE_ID
    assert packet["retired_candidate_status"] == "retired_due_to_insufficient_definition"
    assert packet["current_candidate_revised"] is False
    assert packet["current_candidate_replaced"] is True
    assert packet["no_candidate_selected"] is False


def test_candidate_definition_packet_revision_lane_not_patched() -> None:
    packet = _json(DEFAULT_OUT)
    lane = packet["revision_lane"]
    assert lane["lane_id"] == "revise_current_candidate"
    assert lane["candidate_under_review"] == RETIRED_CANDIDATE_ID
    assert lane["proposed_revised_candidate_id"] == (
        "broader_stress_energy_like_distribution_candidate_v1"
    )
    assert lane["selection_status"] == "not_selected"
    assert lane["selection_licensed"] is False
    assert lane["decision"] == "revision_not_licensed"
    for field in [
        "background_geometry_assumptions",
        "tensor_type",
        "index_placement",
        "regularity_class",
        "test_domain",
        "pairing_rule",
        "linearity_condition",
        "continuity_condition",
        "coordinate_or_covariance_behavior",
    ]:
        assert field in lane["missing_fields"]


def test_candidate_definition_packet_replacement_options_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    options = {row["candidate_id"]: row for row in packet["replacement_options"]}
    assert list(options) == [
        "locally_integrable_symmetric_tensor_candidate_v0",
        SELECTED_REPLACEMENT_CANDIDATE_ID,
        "tensor_density_source_candidate_v0",
        "renormalized_expectation_stress_energy_candidate_v0",
        "action_variation_source_candidate_v0",
    ]
    selected = options[SELECTED_REPLACEMENT_CANDIDATE_ID]
    assert selected["selection_status"] == "selected"
    assert selected["selection_licensed"] is True
    assert selected["candidate_kind"] == SELECTED_REPLACEMENT_CANDIDATE_KIND
    assert selected["regularity"] == "D'(M, Sym^2 TM)"
    assert selected["test_domain"] == TEST_SPACE
    assert selected["functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert selected["pairing_rule"] == SELECTED_PAIRING_RULE
    assert selected["linearity_condition"] == "linear on C_c^infty(M, Sym^2 T*M)"
    assert selected["continuity_condition"] == (
        "continuous for the C_c^infty test-space topology"
    )
    assert selected["tensor_type"] == SELECTED_TENSOR_TYPE
    assert selected["index_placement"] == SELECTED_INDEX_PLACEMENT
    assert selected["action_derived_status"] == "not_claimed"
    for candidate_id, row in options.items():
        if candidate_id == SELECTED_REPLACEMENT_CANDIDATE_ID:
            continue
        assert row["selection_status"] == "not_selected"
        assert row["selection_licensed"] is False
        assert row["unselected_reason"]


def test_candidate_definition_packet_authorizes_only_weak_pairing_retry() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_replacement_candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert packet["selected_replacement_candidate_kind"] == SELECTED_REPLACEMENT_CANDIDATE_KIND
    assert packet["selected_regular_type"] == "D'(M, Sym^2 TM)"
    assert packet["selected_test_domain"] == TEST_SPACE
    assert packet["selected_functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert packet["selected_pairing_rule"] == SELECTED_PAIRING_RULE
    assert packet["linearity_condition"] == "linear on C_c^infty(M, Sym^2 T*M)"
    assert packet["continuity_condition"] == (
        "continuous for the C_c^infty test-space topology"
    )
    assert packet["weak_pairing_retry_authorized"] is True
    assert packet["weak_pairing_retry_target"] == NEXT_TARGET
    assert packet["weak_pairing_completed"] is False
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["weak_pairing_retry"]["status"] == "AUTHORIZED"
    assert progression["action_derivability"]["status"] == "NOT_REACHED"
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"


def test_candidate_definition_packet_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
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
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert build_qft_gr_candidate_definition_revision_or_replacement_packet() == packet
    assert REQUIRED_FUNCTIONAL_CONTRACT in SELECTED_FUNCTIONAL_CONTRACT


def test_candidate_definition_packet_updates_live_target_to_retry() -> None:
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
        "QFTGRCandidateDefinitionRevisionOrReplacementPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_CANDIDATE_DEFINITION_REVISION_OR_REPLACEMENT_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["decision_result"] == DECISION_RESULT
    assert consumed["retired_candidate_id"] == RETIRED_CANDIDATE_ID
    assert consumed["selected_replacement_candidate_id"] == (
        SELECTED_REPLACEMENT_CANDIDATE_ID
    )
    assert consumed["weak_pairing_retry_authorized"] == "yes"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["selected_replacement_candidate_id"] == (
        SELECTED_REPLACEMENT_CANDIDATE_ID
    )
    assert active_row["selected_functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert active_row["weak_pairing_retry_authorized"] == "yes"
    assert active_row["weak_pairing_completed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_candidate_definition_packet_lean_and_surface_mirrors() -> None:
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
        RETIRED_CANDIDATE_ID,
        SELECTED_REPLACEMENT_CANDIDATE_ID,
        DECISION_RESULT,
        SELECTED_FUNCTIONAL_CONTRACT,
        SELECTED_PAIRING_RULE,
        "QFTGRCandidateDefinitionRevisionOrReplacementPacket",
        "prepare_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_candidate_definition_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_candidate_definition_revision_or_replacement_packet_gate.py"
    )
