from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_ck_constraint_functional_definition_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    CONSTRAINT_ACTION_FORM,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LAMBDA_VARIATION_FORM,
    LEAN_PACKET_PATH,
    METRIC_VARIATION_FORM,
    MINIMUM_REQUIRED_FIELDS,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OPTION_CLASS_COUNT,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    PHI_RELEVANT_RECOMMENDED_CLASSES,
    PHI_VARIATION_FORM,
    SCHEMA_ID,
    build_master_action_ck_constraint_functional_definition_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_constraint_functional_definition_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
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
SEAM_REGISTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
CLASS_B_INVENTORY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
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


def test_master_action_ck_definition_packet_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
        SEAM_REGISTRY_PATH,
        CLASS_B_INVENTORY_PATH,
    ]:
        assert path.exists(), path


def test_master_action_ck_definition_packet_accepts_options_indexed_result() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_master_action_ck_constraint_functional_definition_packet() == packet


def test_master_action_ck_definition_packet_records_variation_contracts() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["constraint_action_form"] == CONSTRAINT_ACTION_FORM
    assert packet["lambda_variation_form"] == LAMBDA_VARIATION_FORM
    assert packet["phi_variation_form"] == PHI_VARIATION_FORM
    assert packet["metric_variation_form"] == METRIC_VARIATION_FORM
    assert packet["minimum_required_fields"] == MINIMUM_REQUIRED_FIELDS
    assert packet["option_class_count"] == OPTION_CLASS_COUNT
    assert packet["ck_constraint_functional_options_indexed"] is True
    assert packet["legal_constraint_type_menu_defined"] is True
    assert packet["options_indexed_no_selection"] is True


def test_master_action_ck_definition_packet_indexes_required_options_without_selection() -> None:
    packet = _json(DEFAULT_OUT)
    options = {row["constraint_id"]: row for row in packet["constraint_functional_options"]}
    assert set(options) == {
        "bridge_admissibility_constraint",
        "conservation_constraint",
        "regime_transport_constraint",
        "gauge_current_compatibility_constraint",
        "state_probability_statistical_constraint",
        "information_correlation_timing_constraint",
        "source_admissibility_constraint",
    }
    for row in options.values():
        for field in MINIMUM_REQUIRED_FIELDS:
            assert row[field], (row["constraint_id"], field)
        assert row["selected_for_definition"] is False
    assert packet["existing_registry_class_tokens"] == [
        "TOE_CK_CLASS_COMPATIBILITY_v0",
        "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
        "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
        "TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0",
    ]
    assert packet["phi_relevant_recommended_classes"] == (
        PHI_RELEVANT_RECOMMENDED_CLASSES
    )
    assert options["source_admissibility_constraint"]["phi_relevance"] == "highest"
    assert options["bridge_admissibility_constraint"]["phi_relevance"] == "high"
    assert packet["ck_constraint_functional_family_selected"] is False
    assert packet["ck_phi_relevant_constraint_class_selected"] is False


def test_master_action_ck_definition_packet_blocks_shortcuts() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["concrete_ck_functional_family_found"] is False
    assert packet["concrete_ck_functional_families_found"] == []
    assert packet["ck_constraint_functional_family_defined"] is False
    assert packet["ck_content_fully_defined"] is False
    for key in [
        "ck_content_fully_defined_claimed",
        "phi_generated_by_ck_claimed",
        "derived_v_phi_claimed",
        "potential_derived",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "native_generation_theorem_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    assert "does not fully define C_k content" in packet["non_claim_boundary"]
    assert "does not select a C_k family" in packet["non_claim_boundary"]


def test_master_action_ck_definition_packet_rotates_live_target_to_review() -> None:
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
        "MasterActionCKConstraintFunctionalDefinitionPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["master_action_ck_constraint_functional_definition_packet_prepared"] == "yes"
    assert consumed["ck_constraint_functional_options_indexed"] == "yes"
    assert consumed["ck_constraint_functional_family_selected"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["ck_constraint_functional_definition_packet_review_prepared"] == "no"
    assert active_row["ck_constraint_functional_options_indexed"] == "yes"
    assert active_row["ck_constraint_functional_family_defined"] == "no"
    assert active_row["ck_constraint_functional_family_selected"] == "no"
    assert active_row["ck_content_fully_defined"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["source_conservation_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_master_action_ck_definition_packet_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
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
        PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "MasterActionCKConstraintFunctionalDefinitionPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: review_master_action_ck_constraint_functional_definition_packet_result",
        "S_C = integral_M d^4x sqrt(-g) sum_k lambda_k C_k(g, psi, A, phi, rho)",
        "delta S_C/delta lambda_k = C_k(g, psi, A, phi, rho) = 0",
        "source_admissibility_constraint",
        "bridge_admissibility_constraint",
        "CK_CONSTRAINT_FUNCTIONAL_OPTIONS_INDEXED_NO_SELECTION",
        "C_k content is not fully defined",
        "phi is not generated by C_k",
        "V(phi) is not derived",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_master_action_ck_definition_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_constraint_functional_definition_packet_gate.py"
    )
