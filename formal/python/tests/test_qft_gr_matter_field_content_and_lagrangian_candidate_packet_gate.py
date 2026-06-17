from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_matter_action_functional_candidate_packet_report import (
    DEFAULT_OUT as MATTER_ACTION_PACKET_PATH,
    OUTCOME_ID as MATTER_ACTION_OUTCOME,
)
from formal.python.tools.qft_gr_matter_field_content_and_lagrangian_candidate_packet_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DIRAC_SPINOR_ACTION_FORM,
    EFFECTIVE_QFT_ACTION_FORM,
    FIELD_LAGRANGIAN_RESULT,
    GAUGE_FIELD_ACTION_FORM,
    GENERIC_MATTER_ACTION_FORM,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REAL_SCALAR_ACTION_FORM,
    SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    WEAK_VARIATIONAL_OBLIGATION,
    build_qft_gr_matter_field_content_and_lagrangian_candidate_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_matter_field_content_and_lagrangian_candidate_packet_report.py"
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


def test_field_content_lagrangian_packet_files_exist() -> None:
    assert MATTER_ACTION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_field_content_lagrangian_packet_records_blocked_result() -> None:
    prior = _json(MATTER_ACTION_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == MATTER_ACTION_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["field_content_lagrangian_result"] == FIELD_LAGRANGIAN_RESULT
    assert packet["candidate_id"] == SELECTED_REPLACEMENT_CANDIDATE_ID
    assert packet["functional_contract"] == SELECTED_FUNCTIONAL_CONTRACT
    assert packet["weak_variational_obligation"] == WEAK_VARIATIONAL_OBLIGATION
    assert packet["matter_model_selected"] is False
    assert packet["matter_field_content_selected"] is False
    assert packet["lagrangian_density_selected"] is False
    assert packet["action_generated_source_subclass_selected"] is False
    assert packet["action_derivability_retry_authorized"] is False
    assert packet["toe_matter_sector_selection_required"] is True


def test_field_content_lagrangian_packet_evaluates_required_options_without_shortcut() -> None:
    packet = _json(DEFAULT_OUT)
    options = {row["option_id"]: row for row in packet["matter_model_options"]}
    assert list(options) == [
        "generic_matter_field_bundle_and_local_lagrangian_density",
        "real_scalar_klein_gordon_type_route",
        "gauge_field_maxwell_type_route",
        "dirac_spinor_field_route",
        "effective_qft_action_route",
        "no_field_content_selected",
    ]
    assert options[
        "generic_matter_field_bundle_and_local_lagrangian_density"
    ]["candidate_form"] == GENERIC_MATTER_ACTION_FORM
    assert options["real_scalar_klein_gordon_type_route"][
        "candidate_form"
    ] == REAL_SCALAR_ACTION_FORM
    assert options["gauge_field_maxwell_type_route"][
        "candidate_form"
    ] == GAUGE_FIELD_ACTION_FORM
    assert options["dirac_spinor_field_route"][
        "candidate_form"
    ] == DIRAC_SPINOR_ACTION_FORM
    assert options["effective_qft_action_route"][
        "candidate_form"
    ] == EFFECTIVE_QFT_ACTION_FORM
    for option_id, row in options.items():
        assert row["selection_licensed"] is False, option_id
        assert row["would_prove_arbitrary_distributional_T_action_derived"] is False
        assert row["blocked_by"], option_id
    assert options["real_scalar_klein_gordon_type_route"]["selection_status"] == (
        "candidate_option_recorded_not_selected"
    )
    assert "scalar_field_not_selected_by_toe_matter_sector" in options[
        "real_scalar_klein_gordon_type_route"
    ]["blocked_by"]
    assert options["no_field_content_selected"]["selection_status"] == (
        "blocked_outcome_recorded"
    )


def test_field_content_lagrangian_packet_records_missing_matter_model_data() -> None:
    packet = _json(DEFAULT_OUT)
    required = {row["field_id"]: row for row in packet["required_matter_model_data"]}
    assert required["toe_matter_sector_candidate"]["status"] == "missing"
    assert required["matter_degrees_of_freedom"]["status"] == "missing"
    assert required["lagrangian_density"]["status"] == "missing"
    assert required["variational_rule"]["required"] == WEAK_VARIATIONAL_OBLIGATION
    assert required["variational_rule"]["status"] == "missing"
    assert required["action_generated_source_subclass_contract"]["status"] == (
        "not_selected"
    )
    assert required["stress_energy_matching_obligation"]["status"] == "not_reached"
    assert required["diffeomorphism_or_covariance_structure"][
        "status"
    ] == "not_reached"
    for missing in [
        "toe_matter_sector_candidate",
        "matter_degrees_of_freedom",
        "lagrangian_density",
        "variational_rule",
        "action_generated_source_subclass_contract",
    ]:
        assert missing in packet["missing_matter_model_data"]
    assert "does not determine matter degrees of freedom" in packet[
        "mathematical_statement"
    ]
    assert "not prove that the arbitrary distributional candidate is action-derived" in packet[
        "mathematical_statement"
    ]


def test_field_content_lagrangian_packet_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["arbitrary_distributional_source_action_derived_claimed"] is False
    assert packet["arbitrary_distributional_source_retired"] is False
    assert packet["action_generated_source_subclass_id"] is None
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
        "matter_action_functional_claimed",
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
    assert progression["field_content_and_lagrangian_candidate"]["status"] == "BLOCKED"
    assert progression["field_content_and_lagrangian_candidate"][
        "decision"
    ] == FIELD_LAGRANGIAN_RESULT
    assert progression["action_generated_source_subclass"]["status"] == "NOT_SELECTED"
    assert progression["action_derivability_retry"]["status"] == "NOT_AUTHORIZED"
    assert progression["toe_matter_sector_candidate_selection"][
        "status"
    ] == "NEXT_TARGET_AUTHORIZED"
    assert progression["toe_matter_sector_candidate_selection"]["decision"] == NEXT_TARGET
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert build_qft_gr_matter_field_content_and_lagrangian_candidate_packet() == packet


def test_field_content_lagrangian_packet_updates_live_target_to_matter_sector_selection() -> None:
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
        "QFTGRMatterFieldContentAndLagrangianCandidatePacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["field_content_lagrangian_result"] == FIELD_LAGRANGIAN_RESULT
    assert consumed["matter_model_selected"] == "no"
    assert consumed["action_generated_source_subclass_selected"] == "no"
    assert consumed["action_derivability_retry_authorized"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["field_content_lagrangian_result"] == FIELD_LAGRANGIAN_RESULT
    assert active_row["toe_matter_sector_selection_required"] == "yes"
    assert active_row["matter_model_selected"] == "no"
    assert active_row["lagrangian_density_selected"] == "no"
    assert active_row["action_derivability_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_field_content_lagrangian_packet_lean_and_surface_mirrors() -> None:
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
        FIELD_LAGRANGIAN_RESULT,
        REAL_SCALAR_ACTION_FORM,
        "QFTGRMatterFieldContentAndLagrangianCandidatePacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_toe_matter_sector_candidate_selection_packet",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_field_content_lagrangian_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_matter_field_content_and_lagrangian_candidate_packet_gate.py"
    )
