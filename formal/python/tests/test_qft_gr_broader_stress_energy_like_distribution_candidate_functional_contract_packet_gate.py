from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_report import (
    CANDIDATE_SOURCE_ID,
    CONTRACT_RESULT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PAIRING_FORMULA,
    REQUIRED_FUNCTIONAL_CONTRACT,
    SCHEMA_ID,
    TEST_SPACE,
    build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_report.py"
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


def test_candidate_functional_contract_packet_files_exist() -> None:
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_candidate_functional_contract_packet_records_blocked_contract_result() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["candidate_source_id"] == CANDIDATE_SOURCE_ID
    assert packet["contract_result"] == CONTRACT_RESULT
    assert packet["candidate_functional_contract_constructed"] is False
    assert packet["candidate_functional_contract_rejected"] is False
    assert packet["contract_option_selected"] is False
    assert packet["multiple_candidate_functional_contract_options_recorded"] is True


def test_candidate_functional_contract_packet_has_mathematical_contract_content() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["working_background"] == "(M, g)"
    assert packet["test_space"] == TEST_SPACE
    assert packet["required_functional_contract"] == REQUIRED_FUNCTIONAL_CONTRACT
    assert packet["smooth_or_locally_integrable_pairing_formula"] == PAIRING_FORMULA
    assert "T : D -> R" in packet["proposition_statement"]
    assert "C_c^infty(M, Sym^2 T*M)" in packet["proposition_statement"]
    outputs = packet["mathematical_acceptance_outputs"]
    for key in [
        "definition_supplied",
        "proposition_or_contract_criterion_stated",
        "symbolic_pairing_form_recorded",
        "well_definedness_precheck_attempted",
        "counterexample_or_obstruction_recorded",
        "calculation_blocked_by_missing_formal_input",
    ]:
        assert outputs[key] is True, key
    assert outputs["weak_pairing_completed"] is False


def test_candidate_functional_contract_packet_assesses_required_fields() -> None:
    packet = _json(DEFAULT_OUT)
    fields = {row["field"]: row for row in packet["contract_field_assessment"]}
    for field in [
        "background_spacetime",
        "test_space",
        "test_space_topology",
        "candidate_regularity",
        "tensor_vs_tensor_density_status",
        "index_placement",
        "volume_measure",
        "metric_dependence",
        "support_and_locality_assumptions",
        "linearity",
        "continuity",
        "coordinate_or_covariance_behavior",
        "action_derived_or_merely_source_like_status",
    ]:
        assert field in fields
    assert fields["candidate_regularity"]["status"] == "blocked_unspecified"
    assert fields["linearity"]["status"] == "blocked_not_verified"
    assert fields["continuity"]["status"] == "blocked_not_verified"
    assert packet["blocked_contract_field_count"] >= 8
    for missing in [
        "candidate_regularity_class_not_supplied",
        "tensor_vs_tensor_density_status_not_supplied",
        "index_placement_not_supplied",
        "linear_map_T_from_D_to_R_not_supplied",
        "continuity_bound_or_distribution_order_not_supplied",
        "coordinate_or_covariance_behavior_not_supplied",
    ]:
        assert missing in packet["missing_mathematical_data"]


def test_candidate_functional_contract_packet_records_options_without_selection() -> None:
    packet = _json(DEFAULT_OUT)
    options = {row["option_id"]: row for row in packet["contract_options"]}
    for option_id in [
        "distributional_continuous_linear_functional",
        "smooth_or_locally_integrable_tensor_representative",
        "tensor_density_pairing",
    ]:
        assert options[option_id]["selection_status"] == "not_selected"
        assert options[option_id]["blocked_by"]
    assert options["distributional_continuous_linear_functional"][
        "contract_form"
    ] == REQUIRED_FUNCTIONAL_CONTRACT
    assert options["smooth_or_locally_integrable_tensor_representative"][
        "contract_form"
    ] == PAIRING_FORMULA


def test_candidate_functional_contract_packet_rejects_overreach_and_is_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["well_defined_pairing"] == "not_reached"
    assert packet["weak_pairing_retry_authorized"] is False
    assert packet["weak_pairing_completed"] is False
    assert packet["source_is_action_derived"] == "not_reached"
    assert packet["weak_conservation_verified"] == "not_reached"
    assert packet["bianchi_compatible_source"] == "not_reached"
    assert packet["semiclassical_source_admissible"] == "not_reached"
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
    assert (
        build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet()
        == packet
    )


def test_candidate_functional_contract_packet_updates_live_target_to_result_review() -> None:
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
        "QFTGRBroaderStressEnergyLikeDistributionCandidateFunctionalContractPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "FUNCTIONAL_CONTRACT_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["contract_result"] == CONTRACT_RESULT
    assert consumed["weak_pairing_retry_authorized"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["contract_result"] == CONTRACT_RESULT
    assert active_row["candidate_source_id"] == CANDIDATE_SOURCE_ID
    assert active_row["weak_pairing_retry_authorized"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_candidate_functional_contract_packet_lean_and_surface_mirrors() -> None:
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
        CANDIDATE_SOURCE_ID,
        CONTRACT_RESULT,
        REQUIRED_FUNCTIONAL_CONTRACT,
        PAIRING_FORMULA,
        "QFTGRBroaderStressEnergyLikeDistributionCandidateFunctionalContractPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_qft_gr_broader_stress_energy_like_distribution_candidate_"
        "functional_contract_packet_result",
        "no weak-pairing retry",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_candidate_functional_contract_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_gate.py"
    )
