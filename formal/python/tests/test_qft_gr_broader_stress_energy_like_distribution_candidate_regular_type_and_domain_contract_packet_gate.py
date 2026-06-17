from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet_report import (
    ARTIFACT_ID,
    CANDIDATE_SOURCE_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DENSITY_CONTRACT,
    DISTRIBUTIONAL_CONTRACT,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    OPERATOR_EXPECTATION_CONTRACT,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PAIRING_FORMULA,
    REGULAR_TYPE_DOMAIN_RESULT,
    REQUIRED_FUNCTIONAL_CONTRACT,
    SCHEMA_ID,
    SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT,
    TEST_SPACE,
    build_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet_report.py"
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


def test_regular_type_domain_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_regular_type_domain_packet_records_insufficient_definition_result() -> None:
    review = _json(RESULT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["candidate_source_id"] == CANDIDATE_SOURCE_ID
    assert packet["regular_type_domain_result"] == REGULAR_TYPE_DOMAIN_RESULT
    assert packet["candidate_definition_status"] == (
        "insufficiently_specified_for_regular_type_or_domain_selection"
    )
    assert packet["selected_regular_type"] is None
    assert packet["selected_domain_contract"] is None
    assert packet["regular_type_selected"] is False
    assert packet["domain_contract_selected"] is False
    assert packet["candidate_revision_or_replacement_required"] is True


def test_regular_type_domain_packet_enumerates_all_regular_type_options() -> None:
    packet = _json(DEFAULT_OUT)
    options = {
        row["option_id"]: row for row in packet["regularity_option_assessments"]
    }
    expected = [
        "smooth_symmetric_tensor_field",
        "locally_integrable_tensor_field",
        "tensor_valued_distribution",
        "tensor_density",
        "operator_valued_distribution_expectation_candidate",
        "undefined_or_insufficiently_specified",
    ]
    assert list(options) == expected
    for option_id in expected[:-1]:
        row = options[option_id]
        assert row["selection_status"] == "not_selected"
        assert row["selection_licensed"] is False
        assert row["unselected_reason"]
        assert row["missing_license_fields"]
    assert options["undefined_or_insufficiently_specified"][
        "selection_status"
    ] == "diagnostic_result"
    assert options["undefined_or_insufficiently_specified"][
        "selection_licensed"
    ] is True


def test_regular_type_domain_packet_enumerates_domain_routes_and_volume_distinction() -> None:
    packet = _json(DEFAULT_OUT)
    domains = {row["domain_option_id"]: row for row in packet["domain_option_assessments"]}
    assert domains["smooth_or_l1loc_tensor_domain"]["contract_form"] == (
        SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT
    )
    assert domains["smooth_or_l1loc_tensor_domain"]["pairing_formula"] == (
        PAIRING_FORMULA
    )
    assert domains["smooth_or_l1loc_tensor_domain"]["uses_dVol_g"] is True
    assert domains["distributional_tensor_domain"]["contract_form"] == (
        DISTRIBUTIONAL_CONTRACT
    )
    assert domains["distributional_tensor_domain"]["pairing_formula"] == (
        REQUIRED_FUNCTIONAL_CONTRACT
    )
    assert domains["tensor_density_domain"]["contract_form"] == DENSITY_CONTRACT
    assert domains["tensor_density_domain"]["uses_dVol_g"] is False
    assert domains["tensor_density_domain"]["pairing_formula"] == (
        "direct tensor-density pairing, not tensor times dVol_g"
    )
    assert domains["operator_expectation_domain"]["contract_form"] == (
        OPERATOR_EXPECTATION_CONTRACT
    )
    for row in domains.values():
        assert row["selection_status"] == "not_selected"
        assert row["blocked_by"]


def test_regular_type_domain_packet_records_missing_definition_data() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["test_space"] == TEST_SPACE
    assert packet["required_functional_contract"] == REQUIRED_FUNCTIONAL_CONTRACT
    assert packet["smooth_or_locally_integrable_pairing_formula"] == PAIRING_FORMULA
    assert packet["smooth_or_locally_integrable_contract"] == (
        SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT
    )
    assert packet["distributional_contract"] == DISTRIBUTIONAL_CONTRACT
    assert packet["density_contract"] == DENSITY_CONTRACT
    assert packet["operator_expectation_contract"] == OPERATOR_EXPECTATION_CONTRACT
    assert packet["missing_candidate_definition_data_count"] >= 10
    for missing in [
        "smooth_regular_representative_not_supplied",
        "L1_loc_regular_representative_not_supplied",
        "tensor_valued_distribution_map_not_supplied",
        "tensor_density_status_not_supplied",
        "operator_valued_distribution_expectation_contract_not_supplied",
        "index_placement_not_supplied",
        "metric_dependence_not_supplied",
        "linearity_on_test_space_not_supplied",
        "continuity_for_test_space_topology_not_supplied",
        "coordinate_or_covariance_behavior_not_supplied",
    ]:
        assert missing in packet["missing_candidate_definition_data"]


def test_regular_type_domain_packet_preserves_nonclaims_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["weak_pairing_retry_authorized"] is False
    assert packet["weak_pairing_retry_target"] is None
    assert packet["weak_pairing_completed"] is False
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
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["weak_pairing_retry"]["status"] == "NOT_AUTHORIZED"
    assert progression["action_derivability"]["status"] == "NOT_REACHED"
    assert progression["weak_conservation"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NOT_REACHED"
    assert progression["semiclassical_source_admissibility"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert (
        build_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet()
        == packet
    )


def test_regular_type_domain_packet_updates_live_target_to_revision_packet() -> None:
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
        "QFTGRBroaderStressEnergyLikeDistributionCandidateRegularTypeAndDomainContractPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "REGULAR_TYPE_AND_DOMAIN_CONTRACT_PACKET_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["regular_type_domain_result"] == REGULAR_TYPE_DOMAIN_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["weak_pairing_retry_authorized"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["regular_type_domain_result"] == REGULAR_TYPE_DOMAIN_RESULT
    assert active_row["candidate_source_id"] == CANDIDATE_SOURCE_ID
    assert active_row["weak_pairing_retry_authorized"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_regular_type_domain_packet_lean_and_surface_mirrors() -> None:
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
        REGULAR_TYPE_DOMAIN_RESULT,
        SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT,
        DISTRIBUTIONAL_CONTRACT,
        DENSITY_CONTRACT,
        OPERATOR_EXPECTATION_CONTRACT,
        "QFTGRBroaderStressEnergyLikeDistributionCandidateRegularTypeAndDomainContractPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_candidate_definition_revision_or_replacement_packet",
        "no weak-pairing retry",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_regular_type_domain_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet_gate.py"
    )
