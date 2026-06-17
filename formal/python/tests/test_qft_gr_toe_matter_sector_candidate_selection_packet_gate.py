from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_matter_field_content_and_lagrangian_candidate_packet_report import (
    DEFAULT_OUT as FIELD_LAGRANGIAN_PACKET_PATH,
    OUTCOME_ID as FIELD_LAGRANGIAN_OUTCOME,
)
from formal.python.tools.qft_gr_toe_matter_sector_candidate_selection_packet_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EFFECTIVE_QFT_ACTION_ROUTE_RESULT,
    LEAN_PACKET_PATH,
    MATTER_SECTOR_SELECTION_RESULT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REAL_SCALAR_ACTION_FORM,
    SCHEMA_ID,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_LAGRANGIAN_DENSITY,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    SELECTED_VARIATIONAL_TARGET,
    TOE_NATIVE_MATTER_SECTOR_RESULT,
    build_qft_gr_toe_matter_sector_candidate_selection_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_toe_matter_sector_candidate_selection_packet_report.py"
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


def test_toe_matter_sector_selection_packet_files_exist() -> None:
    assert FIELD_LAGRANGIAN_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_toe_matter_sector_selection_packet_records_provisional_scalar_result() -> None:
    prior = _json(FIELD_LAGRANGIAN_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == FIELD_LAGRANGIAN_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["matter_sector_selection_result"] == MATTER_SECTOR_SELECTION_RESULT
    assert packet["toe_native_matter_sector_result"] == TOE_NATIVE_MATTER_SECTOR_RESULT
    assert packet["effective_qft_action_route_result"] == EFFECTIVE_QFT_ACTION_ROUTE_RESULT
    assert packet["candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert packet["known_matter_model_imported_as_provisional_test_sector"] is True
    assert packet["selected_provisional_matter_sector_id"] == (
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    )
    assert packet["selected_action_generated_source_subclass_id"] == (
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
    )
    assert packet["selected_field_content"] == SELECTED_FIELD_CONTENT
    assert packet["selected_lagrangian_density"] == SELECTED_LAGRANGIAN_DENSITY
    assert packet["selected_matter_action_form"] == REAL_SCALAR_ACTION_FORM
    assert packet["selected_variational_target"] == SELECTED_VARIATIONAL_TARGET
    assert packet["action_derivability_retry_authorized"] is True


def test_toe_matter_sector_selection_routes_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    routes = {row["route_id"]: row for row in packet["route_assessments"]}
    assert list(routes) == [
        "known_real_scalar_provisional_test_sector",
        "abstract_field_bundle_matter_sector",
        "effective_qft_action_route",
        "toe_native_matter_sector",
        "no_matter_sector_selected",
    ]
    scalar = routes["known_real_scalar_provisional_test_sector"]
    assert scalar["selection_status"] == "selected_provisionally"
    assert scalar["selection_licensed"] is True
    assert scalar["selected_matter_sector_id"] == SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    assert scalar["toe_derivation_claimed"] is False
    assert scalar["standard_model_derivation_claimed"] is False
    assert scalar["action_derivability_claimed"] is False
    assert scalar["source_admissibility_claimed"] is False

    abstract = routes["abstract_field_bundle_matter_sector"]
    assert abstract["selection_status"] == "recorded_not_selected"
    assert abstract["selection_licensed"] is False
    assert "field_bundle_E_not_defined" in abstract["blocked_by"]

    effective = routes["effective_qft_action_route"]
    assert effective["selection_status"] == "recorded_not_licensed"
    assert effective["route_result"] == EFFECTIVE_QFT_ACTION_ROUTE_RESULT
    assert effective["selection_licensed"] is False

    native = routes["toe_native_matter_sector"]
    assert native["selection_status"] == "not_yet_defined"
    assert native["route_result"] == TOE_NATIVE_MATTER_SECTOR_RESULT
    assert native["selection_licensed"] is False
    assert "no_preserved_toe_native_matter_sector_artifact" in native["blocked_by"]


def test_toe_matter_sector_selection_contract_preserves_deeper_blocker() -> None:
    packet = _json(DEFAULT_OUT)
    contract = packet["selected_sector_contract"]
    assert contract["matter_sector_id"] == SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    assert contract["selection_scope"] == "provisional_calculation_sandbox_only"
    assert contract["known_model_imported"] is True
    assert contract["field_content"] == SELECTED_FIELD_CONTENT
    assert contract["lagrangian_density"] == SELECTED_LAGRANGIAN_DENSITY
    assert contract["source_subclass_id"] == SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
    assert contract["toe_derivation_claimed"] is False
    assert contract["standard_model_derivation_claimed"] is False
    assert contract["arbitrary_distributional_source_action_derived_claimed"] is False
    assert packet["toe_native_matter_sector_defined"] is False
    assert packet["toe_matter_model_derived"] is False
    assert packet["toe_matter_sector_selected"] is False
    assert packet["standard_model_derivation_claimed"] is False
    assert packet["arbitrary_distributional_source_action_derived_claimed"] is False
    assert packet["arbitrary_distributional_source_replaced_for_retry"] is True


def test_toe_matter_sector_selection_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["matter_model_selected"] is True
    assert packet["matter_field_content_selected"] is True
    assert packet["lagrangian_density_selected"] is True
    assert packet["action_generated_source_subclass_selected"] is True
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
        "matter_action_derivation_claimed",
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
    assert progression["toe_matter_sector_candidate_selection"][
        "status"
    ] == "PROVISIONAL_TEST_SECTOR_SELECTED"
    assert progression["toe_native_matter_sector"]["status"] == "NOT_DEFINED"
    assert progression["effective_qft_action_route"]["status"] == "NOT_LICENSED"
    assert progression["action_derivability_retry"]["status"] == "NEXT_TARGET_AUTHORIZED"
    assert progression["action_derivability_retry"]["decision"] == NEXT_TARGET
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert build_qft_gr_toe_matter_sector_candidate_selection_packet() == packet


def test_toe_matter_sector_selection_updates_live_target_to_action_retry() -> None:
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
        "QFTGRToeMatterSectorCandidateSelectionPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["matter_sector_selection_result"] == MATTER_SECTOR_SELECTION_RESULT
    assert consumed["known_matter_model_imported_as_provisional_test_sector"] == "yes"
    assert consumed["toe_native_matter_sector_defined"] == "no"
    assert consumed["standard_model_derivation_claimed"] == "no"
    assert consumed["action_derivability_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["matter_sector_selection_result"] == MATTER_SECTOR_SELECTION_RESULT
    assert active_row["selected_provisional_matter_sector_id"] == (
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    )
    assert active_row["selected_action_generated_source_subclass_id"] == (
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
    )
    assert active_row["action_derivability_retry_authorized"] == "yes"
    assert active_row["action_derivability_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_toe_matter_sector_selection_lean_and_surface_mirrors() -> None:
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
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
        MATTER_SECTOR_SELECTION_RESULT,
        TOE_NATIVE_MATTER_SECTOR_RESULT,
        "QFTGRToeMatterSectorCandidateSelectionPacket",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_action_derivability_retry_with_provisional_matter_sector",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_toe_matter_sector_selection_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_toe_matter_sector_candidate_selection_packet_gate.py"
    )
