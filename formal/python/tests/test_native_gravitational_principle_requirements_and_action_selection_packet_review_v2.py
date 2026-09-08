from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_review_v2 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_v2_input_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    assert before == after == review.AUTHORITY_AND_PACKET_HASHES


def test_v2_is_blocked_and_automated_lane_is_closed_without_v3() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["primary_diagnostic"] == review.PRIMARY_DIAGNOSTIC
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    closure = report["lane_closure"]
    assert closure["automated_action_selection_tooling_lane_closed"] is True
    assert closure["automatic_v3_authorized"] is False
    assert closure["v3_created"] is False
    assert closure["real_matrix_execution_authorized"] is False


def test_counterfeit_self_attested_project_provider_manufactures_outcome() -> None:
    audit = _report()["counterfeit_project_provider_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == (
        "PROJECT_EVIDENCE_PROVIDER_SELF_ATTESTATION_ACCEPTED"
    )
    assert audit["source_scientific_content"] == "NONE"
    assert audit["counterfeit_cell_count"] == 70
    assert audit["counterfeit_cells_persisted"] is False
    assert audit["counterfeit_cells_are_real_scientific_judgments"] is False
    assert audit["observed_status"] == "SCIENTIFIC_OUTCOME_COMPUTED"
    assert audit["observed_scientific_outcome"] == (
        "ACTION_FAMILY_UNDERDETERMINED"
    )
    assert audit["observed_matching_scientific_outcome_count"] == 1


def test_scientific_relevance_validator_is_only_a_string_label() -> None:
    audit = _report()["scientific_validator_dispatch_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "SCIENTIFIC_RELEVANCE_VALIDATOR_NOT_EXECUTED"
    assert audit["allowed_validator_ids_are_strings_only"] is True
    assert audit["callable_scientific_validator_registry_present"] is False
    assert audit["scientific_relevance_dispatch_present"] is False


def test_controls_share_entry_name_but_bypass_project_provider_path() -> None:
    audit = _report()["shared_path_control_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == (
        "SYNTHETIC_CONTROLS_BYPASS_PROJECT_PROVIDER_VALIDATION"
    )
    assert audit["production_entry_point_id"] == "evaluate_analysis_v2"
    assert audit["all_controls_use_shared_entry_point_id"] is True
    assert audit["control_provider_validation_status"] == (
        "INTERNAL_SYNTHETIC_PROVIDER"
    )
    assert audit["control_records_with_project_attestation_hash_and_validator"] == 0
    assert audit["project_provider_branch_exercised_by_controls"] is False
    assert audit["complete_future_project_path_shared"] is False


def test_production_entry_does_not_revalidate_authority_custody() -> None:
    audit = _report()["production_authority_custody_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "PRODUCTION_AUTHORITY_CUSTODY_NOT_REVALIDATED"
    assert audit["packet_build_performs_authority_hash_validation"] is True
    assert audit["evaluate_analysis_calls_authority_hash_validator"] is False
    assert audit["evaluate_analysis_reads_module_global_bound_requirement_catalog"] is True
    assert audit["evaluate_analysis_reads_module_global_bound_family_catalog"] is True


def test_authority_objects_reject_public_forgery_and_normal_mutation() -> None:
    audit = _report()["authority_object_audit"]
    assert audit["status"] == "PASS"
    assert audit["frozen_field_mutation_rejected"] is True
    assert audit["raw_decision_object_rejected"] is True
    assert audit["raw_decision_object_observed_diagnostic"] == (
        "CALLER_DECISION_BEARING_OBJECT_REJECTED"
    )


def test_missing_project_evidence_fails_before_matrix() -> None:
    audit = _report()["missing_project_evidence_audit"]
    assert audit["status"] == "PASS"
    assert audit["observed_status"] == "PRECHECK_FAILURE"
    assert audit["observed_diagnostic"] == "PROJECT_EVIDENCE_PROVIDER_REQUIRED"
    assert audit["matrix_evaluated"] is False
    assert audit["observed_scientific_outcome"] is None


def test_good_v2_reduction_and_terminal_contracts_are_retained() -> None:
    audit = _report()["retained_contract_audit"]
    assert audit["status"] == "PASS"
    assert set(audit["checks"].values()) == {"PASS"}
    assert audit["retained_control_count"] == audit["retained_control_pass_count"] == 8
    assert audit["boundary_probe_count"] == audit["boundary_probe_pass_count"] == 2
    assert (
        audit["v2_adversarial_control_count"]
        == audit["v2_adversarial_control_pass_count"]
        == 6
    )
    assert audit["outcome_control_count"] == audit["outcome_control_pass_count"] == 6


def test_exactly_four_foundational_findings_are_recorded() -> None:
    report = _report()
    findings = report["findings"]
    assert findings["finding_count"] == findings["foundational_blocking_count"] == 4
    assert [row["diagnostic"] for row in findings["rows"]] == [
        "PROJECT_EVIDENCE_PROVIDER_SELF_ATTESTATION_ACCEPTED",
        "SCIENTIFIC_RELEVANCE_VALIDATOR_NOT_EXECUTED",
        "SYNTHETIC_CONTROLS_BYPASS_PROJECT_PROVIDER_VALIDATION",
        "PRODUCTION_AUTHORITY_CUSTODY_NOT_REVALIDATED",
    ]
    gates = report["review_gates"]
    assert gates["gate_count"] == 7
    assert gates["pass_count"] == 3
    assert gates["failure_count"] == 4


def test_real_analysis_remains_zero_and_exploration_is_nonauthoritative() -> None:
    report = _report()
    scope = report["scope"]
    assert scope["counterfeit_temporary_probe_cells_executed"] == 70
    assert scope["counterfeit_probe_cells_are_real_matrix_cells"] is False
    assert scope["counterfeit_probe_artifacts_persisted"] is False
    assert scope["real_matrix_cells_computed"] == 0
    for key in (
        "real_requirements_family_analysis_executed",
        "real_family_judgment_made",
        "real_equivalence_class_established",
        "real_survivor_matrix_computed",
        "real_scientific_outcome_selected",
        "native_gravitational_principle_identified",
        "new_postulate_authorized",
        "gravitational_action_proposed_or_selected",
        "standard_GR_comparator_activated",
        "automatic_v3_authorized",
        "v3_created",
    ):
        assert scope[key] is False, key
    exploratory = report["exploratory_boundary"]
    assert exploratory["nonauthoritative"] is True
    assert exploratory["manually_adjudicated"] is True
    assert exploratory["real_matrix_population_authorized"] is False
    assert exploratory["survivor_or_action_selection_authorized"] is False


def test_human_review_records_decisive_probe_lane_closure_and_nonclaims() -> None:
    text = (REPO_ROOT / review.REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRIMARY_DIAGNOSTIC,
        "SCIENTIFIC_RELEVANCE_VALIDATOR_NOT_EXECUTED",
        "SYNTHETIC_CONTROLS_BYPASS_PROJECT_PROVIDER_VALIDATION",
        "PRODUCTION_AUTHORITY_CUSTODY_NOT_REVALIDATED",
        "ACTION_FAMILY_UNDERDETERMINED",
        "0 / 70",
        "No V3",
        review.SELECTED_NEXT_TARGET,
        "NONAUTHORITATIVE_MANUALLY_ADJUDICATED_EXPLORATORY_SURVEY_ONLY",
    ):
        assert token in text
