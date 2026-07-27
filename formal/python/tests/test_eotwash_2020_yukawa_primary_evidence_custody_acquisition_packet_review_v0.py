from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_review_v0
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _gates() -> dict[str, dict[str, object]]:
    return {row["gate_id"]: row for row in _report()["review_gates"]["rows"]}


def _probes() -> dict[str, dict[str, object]]:
    return {row["probe_id"]: row for row in _report()["adversarial_no_shortcut_probes"]["rows"]}


def test_review_regenerates_exactly_and_preserves_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    review.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    assert before == after == review.PACKET_HASHES


def test_review_accepts_contract_for_one_bounded_execution() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_packet_review_outcome"] == review.PRINCIPAL_OUTCOME
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    assert report["result_review_target"] == review.RESULT_REVIEW_TARGET


def test_inventory_audit_finds_six_items_and_no_hidden_input() -> None:
    audit = _report()["independent_inventory_audit"]
    assert audit["inventory_item_count"] == 6
    assert audit["complete_item_count_now"] == 0
    assert audit["hidden_decision_bearing_input_found"] is False
    assert audit["newtonian_baseline_location"] == (
        "FORWARD_AND_STATISTICAL_SUFFICIENCY_OBLIGATIONS"
    )
    assert audit["all_items_tied_to_operations"] is True


def test_custody_state_machine_is_ordered_and_file_presence_is_insufficient() -> None:
    audit = _report()["custody_state_machine_audit"]
    assert audit["ordered_states"] == review.STATE_ORDER
    assert audit["required_custody_field_count"] == 12
    assert audit["state_skipping_allowed"] is False
    assert audit["file_presence_implies_verification"] is False
    assert audit["file_presence_implies_completeness"] is False


def test_transition_function_rejects_skips_and_requires_state_conditions() -> None:
    assert review._transition_allowed(
        "IDENTIFIED", "ACQUIRED", custody_fields_complete=True
    ) is True
    assert review._transition_allowed("ACQUIRED", "INGESTED", parsed=True) is True
    assert review._transition_allowed(
        "INGESTED", "VERIFIED", exact_inventory_match=True
    ) is True
    assert review._transition_allowed(
        "VERIFIED", "COMPLETE", inventory_item_complete=True
    ) is True
    assert review._transition_allowed("IDENTIFIED", "COMPLETE", inventory_item_complete=True) is False
    assert review._transition_allowed("ACQUIRED", "VERIFIED", exact_inventory_match=True) is False


def test_all_ten_adversarial_no_shortcut_probes_pass() -> None:
    probes = _report()["adversarial_no_shortcut_probes"]
    assert probes["probe_count"] == probes["pass_count"] == 10
    assert probes["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in probes["rows"])


def test_identified_url_and_acquired_filename_cannot_create_completeness() -> None:
    probes = _probes()
    assert probes["IDENTIFIED_URL_TO_COMPLETE"]["observed"] == "REJECT"
    assert probes["ACQUIRED_FILE_TO_VERIFIED"]["observed"] == "REJECT"
    assert probes["VERIFIED_PARTIAL_ITEM_TO_COMPLETE"]["observed"] == "REJECT"


def test_supporting_prose_and_access_circumvention_are_rejected() -> None:
    probes = _probes()
    assert probes["DISSERTATION_PROSE_SUBSTITUTION"]["observed"] == "REJECT"
    assert probes["ACCESS_CONTROL_CIRCUMVENTION"]["observed"] == "REJECT"


def test_contact_forecast_and_likelihood_shortcuts_are_rejected() -> None:
    probes = _probes()
    assert probes["AUTHOR_CONTACT_DURING_ACQUISITION"]["observed"] == (
        "REJECT_AND_STOP_WITH_CONTACT_REQUIRED"
    )
    assert probes["SYNTHETIC_FORECAST_BYPASS"]["observed"] == "REJECT"
    assert probes["LIKELIHOOD_AFTER_COMPLETE_FILE"]["observed"] == (
        "REJECT_AND_STOP_FOR_RESULT_REVIEW"
    )


def test_all_twenty_one_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 21
    assert gates["failure_count"] == 0
    assert len(_gates()) == 21
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_inventory_covariance_nuisance_forward_and_coverage_gates_pass() -> None:
    gates = _gates()
    for gate_id in (
        "G3_SIX_ITEM_INVENTORY_COVERS_DECISION_BEARING_OPERATIONS",
        "G6_UNCERTAINTY_AND_COVARIANCE_CONTRACT_COMPLETE_IN_SCOPE",
        "G7_FIVE_NUISANCE_PRIOR_CONTRACTS_EXACT",
        "G8_EXTENDED_SOURCE_FORWARD_MODEL_CANNOT_BE_DESCRIPTIVE_ONLY",
        "G9_BOUNDARY_COVERAGE_PROCEDURE_IS_DECISION_BEARING",
    ):
        assert gates[gate_id]["status"] == "PASS"


def test_source_hierarchy_and_supporting_source_firewalls_pass() -> None:
    gates = _gates()
    assert gates["G10_PRIMARY_AUTHENTICATED_SOURCE_HIERARCHY_FINITE"]["status"] == "PASS"
    assert gates["G11_SUPPORTING_SOURCES_CANNOT_REPLACE_PRIMARY_NUMERICAL_EVIDENCE"]["status"] == "PASS"


def test_custody_and_content_verification_firewalls_pass() -> None:
    gates = _gates()
    assert gates["G12_ALL_TWELVE_CUSTODY_FIELDS_MANDATORY"]["status"] == "PASS"
    assert gates["G13_FIVE_CUSTODY_STATES_ORDERED_AND_NONSUBSTITUTABLE"]["status"] == "PASS"
    assert gates["G14_FILE_PRESENCE_CANNOT_CREATE_COMPLETENESS"]["status"] == "PASS"


def test_sufficiency_tests_require_baseline_before_scalar_use() -> None:
    gates = _gates()
    assert gates["G15_FORWARD_MODEL_SUFFICIENCY_TEST_EXACT"]["status"] == "PASS"
    assert gates["G16_STATISTICAL_SUFFICIENCY_REQUIRES_BASELINE_PROFILING_AND_COVERAGE"]["status"] == "PASS"


def test_authorized_acquisition_has_exact_finite_limits() -> None:
    execution = _report()["authorized_acquisition"]
    assert execution["execution_count"] == 1
    assert execution["maximum_non_contact_source_tiers"] == 5
    assert execution["maximum_total_retrieval_attempts"] == 8
    assert execution["maximum_attempts_per_concrete_url"] == 2
    assert execution["maximum_alternative_authenticated_mirrors"] == 2
    assert execution["maximum_interactive_manual_download_sessions"] == 1
    assert execution["interactive_manual_download_allowed"] is True
    assert execution["access_control_circumvention_allowed"] is False


def test_author_contact_fit_forecast_and_reinterpretation_remain_unauthorized() -> None:
    execution = _report()["authorized_acquisition"]
    assert execution["author_or_custodian_contact_authorized"] is False
    assert execution["likelihood_execution_authorized"] is False
    assert execution["synthetic_forecast_authorized"] is False
    assert execution["published_constraint_reinterpretation_authorized"] is False


def test_execution_must_stop_for_independent_result_review() -> None:
    execution = _report()["authorized_acquisition"]
    assert execution["must_stop_at_result_review"] is True
    assert execution["result_review_target"] == review.RESULT_REVIEW_TARGET
    assert any(review.RESULT_REVIEW_TARGET in rule for rule in _report()["binding_execution_rules"])


def test_scope_authorizes_one_acquisition_but_executes_nothing_now() -> None:
    scope = _report()["scope"]
    assert scope["independent_packet_review_executed"] is True
    assert scope["packet_accepted"] is True
    assert scope["one_bounded_acquisition_execution_authorized"] is True
    assert scope["acquisition_executed_now"] is False
    assert scope["supplement_downloaded_or_acquired_now"] is False
    assert scope["author_or_custodian_contact_authorized"] is False
    assert scope["likelihood_execution_authorized"] is False
    assert scope["likelihood_evaluated"] is False


def test_theory_and_downstream_firewalls_remain_closed() -> None:
    scope = _report()["scope"]
    for field in (
        "numerical_lambda_bound_computed",
        "numerical_alpha_bound_computed",
        "beta_zero_adopted",
        "alpha_sign_or_value_adopted",
        "scalar_branch_adopted",
        "native_scalar_bridge_identified",
        "native_gravitational_principle_identified",
        "gravitational_action_selected",
        "matter_sector_selected",
        "orbital_or_light_propagation_analysis_executed",
        "frame_dragging_resumed",
        "master_action_mutated",
    ):
        assert scope[field] is False


def test_current_posture_rotates_to_one_acquisition_execution() -> None:
    posture = _report()["current_posture"]
    assert posture["acquisition_packet_review"] == "ACCEPTED_21_OF_21_GATES"
    assert posture["principal_outcome"] == "PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_READY"
    assert posture["authorized_acquisition_executions"] == 1
    assert posture["acquisition_executed"] == "NO"
    assert posture["required_evidence_items"] == "0_OF_6_COMPLETE"
    assert posture["files_acquired"] == 0
    assert posture["next_authority"] == review.SELECTED_NEXT_TARGET
