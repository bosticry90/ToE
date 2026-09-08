from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _inventory() -> dict[str, dict[str, object]]:
    return {row["item_id"]: row for row in _report()["required_evidence_inventory"]["rows"]}


def test_packet_regenerates_exactly_and_preserves_selection_custody() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    packet.build_packet()
    after = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    assert before == after == packet.AUTHORITY_HASHES


def test_packet_consumes_exact_preparation_target_and_rotates_only_to_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == packet.SELECTED_NEXT_TARGET_KIND


def test_experiment_and_fixed_signal_remain_frozen_without_likelihood() -> None:
    boundary = _report()["experiment_boundary"]
    assert boundary["experiment"] == "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE"
    assert boundary["fixed_signal"] == "A_Y=1/3"
    assert boundary["experiment_scientifically_suitable"] is True
    assert boundary["independent_likelihood_executable_now"] is False


def test_exactly_six_evidence_items_are_required_and_zero_are_complete() -> None:
    inventory = _report()["required_evidence_inventory"]
    assert inventory["item_count"] == 6
    assert inventory["complete_item_count"] == 0
    assert set(_inventory()) == {
        "OBSERVATION_TORQUE_VECTOR",
        "DISPLACEMENT_AND_CONFIGURATION_METADATA",
        "UNCERTAINTY_AND_COVARIANCE_MODEL",
        "FIVE_NUISANCE_PRIOR_CONTRACTS",
        "EXTENDED_SOURCE_TORQUE_FORWARD_MODEL",
        "BOUNDARY_COVERAGE_PROCEDURE",
    }
    assert all(row["complete"] is False for row in inventory["rows"])


def test_observation_vector_requires_95_by_3_values_and_mapping() -> None:
    row = _inventory()["OBSERVATION_TORQUE_VECTOR"]
    assert row["expected_count"] == 285
    assert row["expected_shape"] == "95 settings x 3 harmonics"
    assert "row identifiers and ordering" in row["required_fields"]
    assert "data-selection or exclusion flags" in row["required_fields"]


def test_displacement_metadata_is_separate_decision_bearing_evidence() -> None:
    row = _inventory()["DISPLACEMENT_AND_CONFIGURATION_METADATA"]
    assert "x y s displacement metadata for every setting" in row["required_fields"]
    assert "ordering key matching the torque vector" in row["required_fields"]
    assert "correct physical configuration" in row["required_operation"]


def test_uncertainty_contract_requires_covariance_or_equivalent_model() -> None:
    row = _inventory()["UNCERTAINTY_AND_COVARIANCE_MODEL"]
    assert "covariance matrix or equivalent generative error model" in row["required_fields"]
    assert "regularization and conditioning rules" in row["required_fields"]


def test_all_five_nuisance_contracts_require_numerical_and_operational_fields() -> None:
    row = _inventory()["FIVE_NUISANCE_PRIOR_CONTRACTS"]
    assert row["expected_count"] == 5
    assert row["parameter_ids"] == ["x0", "y0", "s0", "surface_roughness", "gamma"]
    for phrase in (
        "central value and width",
        "cross-parameter covariance or declared independence",
        "profiling marginalization or fixing rule",
        "exact forward-model entry point",
    ):
        assert phrase in row["required_fields"]


def test_forward_model_requires_newtonian_and_yukawa_three_harmonic_paths() -> None:
    row = _inventory()["EXTENDED_SOURCE_TORQUE_FORWARD_MODEL"]
    assert "Newtonian baseline implementation" in row["required_fields"]
    assert "Yukawa implementation for arbitrary lambda0 and fixed A_Y=1/3" in row["required_fields"]
    assert "three predicted torque harmonics" in row["required_operation"]


def test_boundary_coverage_inventory_is_not_a_published_curve() -> None:
    row = _inventory()["BOUNDARY_COVERAGE_PROCEDURE"]
    assert "lambda0 to zero boundary treatment" in row["required_fields"]
    assert "random-seed or reproducibility policy" in row["required_fields"]
    assert "calibrate valid exclusion coverage" in row["required_operation"]


def test_source_hierarchy_has_five_noncontact_tiers_and_separate_contact() -> None:
    hierarchy = _report()["source_hierarchy"]
    assert hierarchy["source_count"] == 6
    assert hierarchy["non_contact_source_count"] == 5
    assert hierarchy["contact_source_count"] == 1
    assert [row["priority"] for row in hierarchy["rows"]] == [1, 2, 3, 4, 5, 6]
    assert hierarchy["rows"][-1]["current_status"] == "NOT_AUTHORIZED_TERMINAL_OUTCOME_ONLY"


def test_official_aps_supplement_identifier_is_recorded_without_acquisition() -> None:
    first = _report()["source_hierarchy"]["rows"][0]
    assert first["source_id"] == "APS_OFFICIAL_SUPPLEMENTAL_DEPOSIT"
    assert first["identifier"] == (
        "https://link.aps.org/supplemental/10.1103/PhysRevLett.124.101101"
    )
    assert first["current_status"] == "IDENTIFIED_EXPECTED_URL_CONTENT_NOT_ACQUIRED"
    assert first["may_execute_now"] is False


def test_supporting_sources_and_unverified_substitutions_cannot_replace_primary_evidence() -> None:
    hierarchy = _report()["source_hierarchy"]
    assert "values inferred from dissertation prose" in hierarchy["forbidden_substitutions"]
    assert "plot digitization" in hierarchy["forbidden_substitutions"]
    assert "unverified file-sharing mirrors" in hierarchy["forbidden_substitutions"]


def test_custody_record_has_twelve_exact_fields() -> None:
    custody = _report()["custody_contract"]
    assert custody["required_field_count"] == 12
    assert custody["required_fields"] == packet.CUSTODY_FIELDS


def test_custody_states_are_ordered_nonsubstitutable_and_currently_zero() -> None:
    custody = _report()["custody_contract"]
    assert custody["state_count"] == 5
    assert custody["ordered_states"] == ["IDENTIFIED", "ACQUIRED", "INGESTED", "VERIFIED", "COMPLETE"]
    assert custody["state_skipping_allowed"] is False
    assert custody["file_presence_implies_completeness"] is False
    assert custody["current_acquired_object_count"] == 0
    assert custody["current_ingested_object_count"] == 0
    assert custody["current_verified_item_count"] == 0
    assert custody["current_complete_item_count"] == 0


def test_content_verification_allows_partial_findings_without_false_success() -> None:
    contract = _report()["content_verification_contract"]
    assert contract["supplement_receipt_is_success"] is False
    assert contract["partial_results_allowed"] is True
    assert contract["principal_status_count"] == 1
    assert contract["subordinate_finding_cap"] == 6


def test_forward_model_sufficiency_has_six_unexecuted_obligations() -> None:
    contract = _report()["forward_model_sufficiency_test"]
    assert contract["status"] == "PREPARED_NOT_EXECUTED"
    assert contract["obligation_count"] == 6
    assert len(contract["obligations"]) == 6
    assert contract["published_newtonian_baseline_required_before_scalar"] is True
    assert contract["published_newtonian_baseline"] == "chi_squared=275.0 for nu=285, P=0.654"


def test_statistical_sufficiency_requires_baseline_profiling_and_coverage() -> None:
    contract = _report()["statistical_sufficiency_test"]
    assert contract["status"] == "PREPARED_NOT_EXECUTED"
    assert contract["obligation_count"] == 5
    assert contract["all_files_present_can_substitute_for_baseline_reproduction"] is False
    text = " ".join(contract["obligations"])
    for token in ("baseline", "five-nuisance", "boundary-aware", "frozen tolerance"):
        assert token in text


def test_acquisition_protocol_has_finite_attempt_mirror_and_ingestion_limits() -> None:
    protocol = _report()["bounded_acquisition_protocol"]
    assert protocol["status"] == "PREPARED_NOT_AUTHORIZED_FOR_EXECUTION"
    assert protocol["maximum_non_contact_source_tiers"] == 5
    assert protocol["maximum_total_retrieval_attempts"] == 8
    assert protocol["maximum_attempts_per_concrete_url"] == 2
    assert protocol["maximum_alternative_authenticated_mirrors"] == 2
    assert protocol["maximum_interactive_manual_download_sessions"] == 1
    assert protocol["access_control_circumvention_allowed"] is False
    assert protocol["author_contact_status"] == "NOT_AUTHORIZED_TERMINAL_OUTCOME_ONLY"


def test_all_nine_acquisition_terminal_outcomes_are_available() -> None:
    outcomes = _report()["acquisition_terminal_outcomes"]
    assert outcomes["outcome_count"] == 9
    assert outcomes["one_principal_outcome_required"] is True
    assert outcomes["multiple_subordinate_findings_allowed"] is True
    names = {row["outcome"] for row in outcomes["rows"]}
    assert {
        "SUPPLEMENT_ACQUIRED_AND_COMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_OBSERVATION_VECTOR_INCOMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_COVARIANCE_INCOMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_NUISANCE_PRIORS_INCOMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_FORWARD_MODEL_INCOMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_COVERAGE_PROCEDURE_INCOMPLETE",
        "SUPPLEMENT_IDENTIFIED_BUT_NOT_INGESTIBLE",
        "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED",
        "PRIMARY_EVIDENCE_NOT_OBTAINABLE_WITHIN_BOUNDED_ROUTE",
    } == names


def test_parallel_computational_lanes_are_useful_but_separately_unauthorized() -> None:
    lanes = _report()["parallel_computational_lanes"]
    assert lanes["synthetic_forward_model_and_sensitivity_forecast"] == (
        "SCIENTIFICALLY_VALUABLE_FRESH_AUTHORITY_REQUIRED"
    )
    assert lanes["supplied_published_constraint_reinterpretation"] == (
        "SCIENTIFICALLY_VALUABLE_FRESH_AUTHORITY_REQUIRED"
    )
    assert lanes["independent_real_data_reanalysis"] == "REMAINS_BLOCKED"
    assert len(lanes["binding_claim_separation"]) == 4


def test_all_twenty_four_preparation_controls_pass() -> None:
    controls = _report()["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 24
    assert controls["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in controls["rows"])


def test_scope_authorizes_preparation_and_nothing_external_or_empirical() -> None:
    scope = _report()["scope"]
    allowed_true = {"packet_preparation_executed"}
    assert scope["packet_preparation_executed"] is True
    for key, value in scope.items():
        if key not in allowed_true:
            assert value is False, key


def test_current_posture_stops_at_independent_packet_review() -> None:
    posture = _report()["current_posture"]
    assert posture["acquisition_packet"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert posture["required_evidence_items"] == "0_OF_6_COMPLETE"
    assert posture["supplement_acquisition"] == "NOT_STARTED"
    assert posture["author_contact"] == "NOT_AUTHORIZED"
    assert posture["likelihood"] == "NOT_EXECUTED"
    assert posture["next_authority"] == packet.SELECTED_NEXT_TARGET
