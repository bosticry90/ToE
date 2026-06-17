from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    ACTION_DERIVABILITY_RESULT,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    COVARIANT_VARIATION_FORM,
    DEFAULT_OUT,
    INDEX_BRIDGE,
    LEAN_PACKET_PATH,
    METRIC_VARIATION_CONVENTION,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIOR_CONTRACT_PAIRING_FORM,
    SCALAR_ACTION,
    SCALAR_LAGRANGIAN,
    SCHEMA_ID,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    TOE_MATTER_SELECTION_PACKET_PATH,
    TOE_NATIVE_MATTER_SECTOR_RESULT,
    WEAK_PAIRING_TRANSLATION,
    build_qft_gr_action_derivability_retry_with_provisional_matter_sector,
)
from formal.python.tools.qft_gr_toe_matter_sector_candidate_selection_packet_report import (
    OUTCOME_ID as TOE_MATTER_SELECTION_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_action_derivability_retry_with_provisional_matter_sector_report.py"
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


def test_action_derivability_retry_files_exist() -> None:
    assert TOE_MATTER_SELECTION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_action_derivability_retry_records_scalar_derivation() -> None:
    prior = _json(TOE_MATTER_SELECTION_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == TOE_MATTER_SELECTION_OUTCOME
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
    assert packet["selected_provisional_matter_sector_id"] == (
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    )
    assert packet["selected_action_generated_source_subclass_id"] == (
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
    )
    assert packet["field_content"] == SELECTED_FIELD_CONTENT
    assert packet["scalar_action"] == SCALAR_ACTION
    assert packet["lagrangian_density"] == SCALAR_LAGRANGIAN
    assert packet["metric_variation_convention"] == METRIC_VARIATION_CONVENTION
    assert packet["stress_energy_covariant_expression"] == (
        STRESS_ENERGY_COVARIANT_EXPRESSION
    )
    assert packet["covariant_variation_form"] == COVARIANT_VARIATION_FORM
    assert packet["prior_contract_pairing_form"] == PRIOR_CONTRACT_PAIRING_FORM
    assert packet["index_bridge"] == INDEX_BRIDGE
    assert packet["weak_pairing_translation"] == WEAK_PAIRING_TRANSLATION


def test_action_derivability_retry_derivation_steps_are_substantive() -> None:
    packet = _json(DEFAULT_OUT)
    steps = {row["step_id"]: row for row in packet["derivation_steps"]}
    assert list(steps) == [
        "state_action",
        "state_variation_convention",
        "vary_lagrangian",
        "vary_volume",
        "combine_variation",
        "read_stress_energy",
        "translate_to_prior_pairing",
    ]
    assert SCALAR_ACTION in steps["state_action"]["mathematical_content"]
    assert "delta L_m" in steps["vary_lagrangian"]["mathematical_content"]
    assert "delta(dVol_g)" in steps["vary_volume"]["mathematical_content"]
    assert COVARIANT_VARIATION_FORM in steps["combine_variation"][
        "mathematical_content"
    ]
    assert STRESS_ENERGY_COVARIANT_EXPRESSION in steps["read_stress_energy"][
        "mathematical_content"
    ]
    assert WEAK_PAIRING_TRANSLATION in steps["translate_to_prior_pairing"][
        "mathematical_content"
    ]
    assert "T_{mu nu}" in packet["stress_energy_covariant_expression"]
    assert "T^{mu nu}" in packet["stress_energy_contravariant_expression"]


def test_action_derivability_retry_preserves_nonclaims_and_next_stage() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["action_derivability_constructed"] is True
    assert packet["action_derivability_constructed_scope"] == (
        "provisional real-scalar calculation sandbox only"
    )
    assert packet["toe_native_matter_sector_result"] == TOE_NATIVE_MATTER_SECTOR_RESULT
    for key in [
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "arbitrary_distributional_source_action_derived_claimed",
        "arbitrary_distributional_source_promoted",
        "source_admissibility_claimed",
        "source_admissibility_completed",
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
    assert progression["action_derivability_retry"][
        "status"
    ] == "CONSTRUCTED_FOR_PROVISIONAL_SCALAR_TEST_SECTOR"
    assert progression["weak_pairing_translation"][
        "status"
    ] == "CONSTRUCTED_WITH_INDEX_CONVENTION"
    assert progression["weak_conservation"]["status"] == "NEXT_TARGET_AUTHORIZED"
    assert progression["weak_conservation"]["decision"] == NEXT_TARGET
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert build_qft_gr_action_derivability_retry_with_provisional_matter_sector() == packet


def test_action_derivability_retry_updates_live_target_to_weak_conservation() -> None:
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
        "QFTGRActionDerivabilityRetryWithProvisionalMatterSector.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_ACTION_DERIVABILITY_RETRY_WITH_PROVISIONAL_MATTER_SECTOR_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert consumed["stress_energy_expression_derived"] == "yes"
    assert consumed["weak_pairing_translation_stated"] == "yes"
    assert consumed["toe_native_matter_derivation_claimed"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert active_row["selected_provisional_matter_sector_id"] == (
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    )
    assert active_row["weak_conservation_test_authorized"] == "yes"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["Bianchi_compatibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_action_derivability_retry_lean_and_surface_mirrors() -> None:
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
        ACTION_DERIVABILITY_RESULT,
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
        STRESS_ENERGY_COVARIANT_EXPRESSION,
        "QFTGRActionDerivabilityRetryWithProvisionalMatterSector",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_action_derivability_retry_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_action_derivability_retry_with_provisional_matter_sector_gate.py"
    )
