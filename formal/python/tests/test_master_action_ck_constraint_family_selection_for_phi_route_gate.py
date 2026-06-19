from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.master_action_ck_constraint_family_selection_for_phi_route_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALTERNATE_SELECTOR_PRIORITY,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFERRED_ALTERNATE_CK_OPTION_CLASS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    RECOMMENDED_SELECTOR_PRIORITY,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SELECTION_RESULT,
    SOURCE_ROUTE_REFERENCE_PATTERN,
    build_master_action_ck_constraint_family_selection_for_phi_route,
)
from formal.python.tools.master_action_ck_constraint_functional_definition_packet_result_review_report import (
    DEFAULT_OUT as CK_DEFINITION_REVIEW_PATH,
    OUTCOME_ID as CK_DEFINITION_REVIEW_OUTCOME,
)
from formal.python.tools.qft_gr_provisional_scalar_classical_source_route_witness_closeout_report import (
    DEFAULT_OUT as SCALAR_WITNESS_CLOSEOUT_PATH,
    OUTCOME_ID as SCALAR_WITNESS_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "master_action_ck_constraint_family_selection_for_phi_route_report.py"
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
CURRENT_AUTHORITY_AGGREGATE_PATH = (
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


def test_ck_family_selection_files_exist() -> None:
    for path in [
        CK_DEFINITION_REVIEW_PATH,
        SCALAR_WITNESS_CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_selection_selects_source_admissibility_family_only() -> None:
    review = _json(CK_DEFINITION_REVIEW_PATH)
    witness = _json(SCALAR_WITNESS_CLOSEOUT_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == CK_DEFINITION_REVIEW_OUTCOME
    assert witness["outcome_id"] == SCALAR_WITNESS_CLOSEOUT_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["selection_result"] == SELECTION_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert packet["selected_ck_option_class"] == RECOMMENDED_SELECTOR_PRIORITY
    assert packet["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert (
        packet["deferred_alternate_ck_option_class"]
        == DEFERRED_ALTERNATE_CK_OPTION_CLASS
        == ALTERNATE_SELECTOR_PRIORITY
    )
    assert (
        build_master_action_ck_constraint_family_selection_for_phi_route()
        == packet
    )


def test_ck_family_selection_criteria_and_family_options_are_bounded() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selection_criteria_count"] == 10
    assert packet["selection_criteria_accepted_count"] == 10
    assert {row["row_id"] for row in packet["selection_criteria"]} == {
        "selector_consumes_current_target",
        "ck_option_index_review_accepted",
        "candidate_set_is_source_or_bridge",
        "scalar_witness_supplies_source_reference_pattern",
        "source_admissibility_selected_as_nearest_phi_family",
        "bridge_admissibility_deferred_not_rejected",
        "selection_is_abstract_family_not_concrete_functional",
        "next_candidate_packet_selected",
        "no_ck_variation_or_phi_generation",
        "no_closure_promotion_or_empirical_claim",
    }
    assert packet["source_route_reference_pattern"] == SOURCE_ROUTE_REFERENCE_PATTERN
    assert packet["candidate_family_option_count"] == 2
    assert packet["candidate_family_options_selected_count"] == 1
    assert packet["candidate_family_options_deferred_count"] == 1
    options = {
        row["constraint_option_class"]: row
        for row in packet["candidate_family_options"]
    }
    assert options["source_admissibility_constraint"]["selection_status"] == (
        "selected_as_abstract_option_family"
    )
    assert options["bridge_admissibility_constraint"]["selection_status"] == (
        "deferred_not_rejected"
    )
    assert options["source_admissibility_constraint"]["concrete_functional_defined"] is False
    assert options["source_admissibility_constraint"]["ck_variation_executed"] is False
    assert options["source_admissibility_constraint"]["physical_law_claimed"] is False


def test_ck_family_selection_blocks_functional_variation_and_promotions() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["ck_constraint_family_selection_executed"] is True
    assert packet["source_admissibility_constraint_family_selected"] is True
    assert packet["bridge_admissibility_constraint_family_deferred"] is True
    assert packet["selected_family_is_abstract_option_class"] is True
    assert packet["candidate_packet_authorized"] is True
    for key in [
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "ck_functional_formula_selected",
        "ck_variation_executed",
        "ck_variation_authorized",
        "ck_family_claimed_as_physical_law",
        "phi_generated_by_ck_claimed",
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
        "standard_model_derivation_claimed",
        "native_generation_theorem_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert packet[key] is False, key
    assert "abstract source-admissibility constraint family" in (
        packet["non_claim_boundary"]
    )
    assert "does not select or define a concrete C_k functional" in (
        packet["non_claim_boundary"]
    )
    assert "C_k does not yet generate phi" in packet["non_claim_boundary"]


def test_ck_family_selection_validation_policy_records_timeout_boundary() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_ck_family_selection_rotates_live_target_to_candidate_packet() -> None:
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
        "MasterActionCKConstraintFamilySelectionForPhiRoute.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "MASTER_ACTION_CK_CONSTRAINT_FAMILY_SELECTION_FOR_PHI_ROUTE_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert consumed["concrete_ck_functional_selected"] == "no"
    assert consumed["ck_variation_executed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["selection_result"] == OUTCOME_ID
    assert active_row["candidate_packet_authorized"] == "yes"
    assert active_row["candidate_packet_prepared"] == "no"
    assert active_row["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert active_row["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert active_row["concrete_ck_functional_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_ck_family_selection_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            CURRENT_AUTHORITY_AGGREGATE_PATH,
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
        SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "MasterActionCKConstraintFamilySelectionForPhiRoute",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_source_admissibility_ck_constraint_candidate_packet",
        SELECTED_CK_CONSTRAINT_FAMILY,
        "source-admissibility constraint family",
        "abstract source-admissibility constraint family",
        "does not select or define a concrete C_k functional",
        "C_k remains inactive and undefined",
        "V(phi) remains smooth bounded-below but not derived",
        "C_k does not yet generate phi",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_ck_family_selection_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_ck_constraint_family_selection_for_phi_route_gate.py"
    )
