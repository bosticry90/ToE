from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_candidate_definition_revision_or_replacement_packet_report import (
    DEFAULT_OUT as CANDIDATE_DEFINITION_PACKET_PATH,
    OUTCOME_ID as CANDIDATE_DEFINITION_OUTCOME,
)
from formal.python.tools.qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet_report import (
    ACTION_DERIVABILITY_STATUS,
    ARTIFACT_ID,
    CALCULATION_RESULT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DISTRIBUTIONAL_REGULARITY,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_INDEX_PLACEMENT,
    SELECTED_PAIRING_RULE,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    SELECTED_REPLACEMENT_CANDIDATE_KIND,
    SELECTED_TENSOR_TYPE,
    TEST_SPACE,
    WELL_DEFINED_PAIRING_SCOPE,
    build_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet_report.py"
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


def test_weak_pairing_retry_packet_files_exist() -> None:
    assert CANDIDATE_DEFINITION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_weak_pairing_retry_packet_constructs_restricted_pairing() -> None:
    prior = _json(CANDIDATE_DEFINITION_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == CANDIDATE_DEFINITION_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["calculation_result"] == CALCULATION_RESULT
    assert packet["well_defined_pairing"] is True
    assert packet["well_defined_pairing_scope"] == WELL_DEFINED_PAIRING_SCOPE
    assert packet["weak_pairing_constructed"] is True
    assert packet["weak_pairing_completed"] is True
    assert packet["weak_pairing_completion_scope"] == WELL_DEFINED_PAIRING_SCOPE


def test_weak_pairing_retry_packet_binds_selected_contract() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert packet["candidate_kind"] == SELECTED_REPLACEMENT_CANDIDATE_KIND
    assert packet["candidate_regular_type"] == DISTRIBUTIONAL_REGULARITY
    assert packet["candidate_tensor_type"] == SELECTED_TENSOR_TYPE
    assert packet["candidate_index_placement"] == SELECTED_INDEX_PLACEMENT
    assert packet["test_domain"] == TEST_SPACE
    assert packet["functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert packet["pairing_definition"] == SELECTED_PAIRING_RULE
    assert packet["mathematical_statement"] == (
        "Given T in D'(M, Sym^2 TM) and h in C_c^infty(M, Sym^2 T*M), "
        "define <T, h> := T(h). The pairing is well-defined as a real "
        "number by the selected continuous linear functional contract."
    )


def test_weak_pairing_retry_packet_records_actual_calculation_steps() -> None:
    packet = _json(DEFAULT_OUT)
    steps = {row["step_id"]: row for row in packet["calculation_steps"]}
    assert list(steps) == [
        "bind_selected_candidate",
        "bind_test_domain",
        "bind_distributional_contract",
        "define_weak_pairing",
        "well_definedness_check",
    ]
    assert steps["bind_test_domain"]["statement"] == f"D = {TEST_SPACE}"
    assert steps["bind_distributional_contract"]["statement"] == (
        SELECTED_FUNCTIONAL_CONTRACT
    )
    assert steps["define_weak_pairing"]["statement"] == SELECTED_PAIRING_RULE
    assert steps["define_weak_pairing"]["result"] == "definition_supplied"
    assert steps["well_definedness_check"]["result"] == WELL_DEFINED_PAIRING_SCOPE
    for row in steps.values():
        assert row["passed"] is True


def test_weak_pairing_retry_packet_authorizes_action_derivability_next_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["action_derivability_status"] == ACTION_DERIVABILITY_STATUS
    assert packet["action_derivability_next_target_authorized"] is True
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["weak_pairing_retry"]["status"] == "COMPLETED_RESTRICTED"
    assert progression["action_derivability"]["status"] == "NEXT_TARGET_AUTHORIZED"
    assert progression["action_derivability"]["decision"] == NEXT_TARGET
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"


def test_weak_pairing_retry_packet_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["weak_pairing_not_physical_source_claim"] is True
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
        "conservation_claimed",
        "weak_conservation_claimed",
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
    assert (
        build_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet()
        == packet
    )


def test_weak_pairing_retry_packet_updates_live_target_to_action_derivability() -> None:
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
        "QFTGRWeakPairingRetryForSelectedCandidateFunctionalContractPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_FUNCTIONAL_"
        "CONTRACT_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["calculation_result"] == CALCULATION_RESULT
    assert consumed["well_defined_pairing"] == "yes"
    assert consumed["weak_pairing_completed"] == "yes"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert active_row["functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert active_row["well_defined_pairing"] == "yes"
    assert active_row["action_derivability_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_weak_pairing_retry_packet_lean_and_surface_mirrors() -> None:
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
        SELECTED_FUNCTIONAL_CONTRACT,
        SELECTED_PAIRING_RULE,
        CALCULATION_RESULT,
        WELL_DEFINED_PAIRING_SCOPE,
        "QFTGRWeakPairingRetryForSelectedCandidateFunctionalContractPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_weak_pairing_retry_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet_gate.py"
    )
