from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    minimal_native_continuum_gravitational_sector_contract_packet_review_v0 as review,
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


def test_review_preserves_every_frozen_authority_and_source_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_SOURCE_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == review.AUTHORITY_AND_SOURCE_HASHES


def test_review_consumes_packet_and_returns_exact_terminal_block() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
    assert report["primary_diagnostic"] == (
        "NO_BOUND_NATIVE_GRAVITATIONAL_PRINCIPLE_OR_POSTULATE"
    )
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "FRESH_FULL_PRIORITY_RESPONSE_SELECTION_ONLY"
    )


def test_contract_design_passes_without_creating_theory() -> None:
    design = _report()["contract_design_review"]
    assert design["status"] == "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT"
    assert design["provenance_class_count"] == 3
    assert design["metric_field_count"] == 1
    assert design["completeness_gate_count"] == 12
    assert design["recovery_stage_count"] == 10
    assert design["outcome_count"] == 6
    assert design["atomic_control_count"] == 8
    assert design["SI_and_compact_support_contract_complete"] is True
    assert design["generic_matter_notation_is_not_existing_action"] is True
    assert design["authority_firewalls_complete"] is True


def test_synthetic_positive_contract_passes_guard_preflight() -> None:
    assert review._first_control_diagnostic(review.BASELINE_SYNTHETIC_CONTRACT) == "PASS"
    controls = _report()["control_execution"]
    assert controls["positive_baseline_passed"] is True


def test_all_eight_atomic_controls_produce_exact_first_diagnostic() -> None:
    controls = _report()["control_execution"]
    assert controls["control_count"] == len(controls["rows"]) == 8
    assert controls["passed_count"] == 8
    assert controls["all_atomic_and_exact"] is True
    for row in controls["rows"]:
        assert row["mutation_count"] == 1
        assert row["observed_diagnostic"] == row["expected_diagnostic"]
        assert row["passed"] is True


def test_fail_fast_review_stops_at_native_principle_gate() -> None:
    gates = _report()["fail_fast_review"]
    assert gates["gate_count"] == len(gates["rows"]) == 8
    assert gates["pass_count"] == 4
    assert gates["failure_count"] == 1
    assert gates["not_evaluated_count"] == 3
    assert gates["first_failed_gate_order"] == 5
    assert gates["rows"] == review.GATE_RESULTS


def test_no_project_principle_postulate_or_structural_alias_selects_action() -> None:
    principle = _report()["native_principle_review"]
    assert principle["status"] == "FAIL"
    for key in (
        "project_principle_bound_that_selects_action",
        "derived_action_family_bound",
        "explicit_postulated_native_candidate_selected",
        "schematic_master_action_selects_candidate",
        "C_k_firewall_selects_candidate",
        "Rep32_selects_continuum_candidate",
        "GR01_selects_continuum_candidate",
    ):
        assert principle[key] is False, key
    assert principle["standard_GR_comparator_exists"] is True
    assert principle["standard_GR_comparator_is_native"] is False


def test_missing_matter_action_is_confirmed_secondary_not_primary() -> None:
    matter = _report()["matter_coupling_posture"]
    assert matter["current_matter_field_content"] == "NOT_SELECTED"
    assert matter["current_matter_lagrangian"] == "NOT_SELECTED"
    assert matter["variation_derived_stress_energy"] == "NOT_AVAILABLE"
    assert matter["secondary_block_confirmed"] is True
    assert matter["selected_as_primary_outcome"] is False
    assert matter["reason_not_primary"] == "NATIVE_PRINCIPLE_GATE_FAILS_FIRST"


def test_no_candidate_satisfaction_or_recovery_stage_is_evaluated() -> None:
    posture = _report()["candidate_satisfaction_posture"]
    assert posture["candidate_formula"] == "NOT_PROPOSED_OR_SELECTED"
    assert posture["candidate_dimensions"] == "NOT_EVALUATED"
    assert posture["candidate_boundary_variation"] == "NOT_EVALUATED"
    assert posture["candidate_symmetry_identity"] == "NOT_EVALUATED"
    assert posture["candidate_matter_source"] == "NOT_EVALUATED"
    assert posture["metric_variation"] == "NOT_EXECUTED"
    assert posture["recovery_stages_executed"] == 0


def test_exactly_one_of_six_outcomes_is_selected() -> None:
    outcomes = _report()["outcome_adjudication"]
    assert outcomes["outcome_count"] == len(outcomes["rows"]) == 6
    assert outcomes["selected_outcome_count"] == 1
    assert outcomes["rows"] == review.OUTCOME_ADJUDICATION
    selected = [row for row in outcomes["rows"] if row["status"] == "SELECTED"]
    assert [row["outcome"] for row in selected] == [
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
    ]


def test_later_candidate_first_vs_no_go_fork_is_not_selected() -> None:
    report = _report()
    assert len(report["fresh_response_options"]) == 4
    assert all(row["authorized_now"] is False for row in report["fresh_response_options"])
    assert report["scope"]["requirements_no_go_route_selected"] is False
    assert report["scope"]["native_postulate_selected"] is False
    assert report["scope"]["standard_GR_comparator_activated"] is False


def test_retained_scientific_posture_is_precise() -> None:
    posture = _report()["retained_scientific_posture"]
    assert posture["contract_design"] == "ACCEPTED_COMPLETE_BOUNDED_REVIEW_CONTRACT"
    assert posture["native_gravitational_principle"] == "NOT_FOUND"
    assert posture["native_gravitational_candidate"] == "NOT_PROPOSED_OR_SELECTED"
    assert posture["matter_action"] == "NOT_DEFINED"
    assert posture["historical_master_action"] == "SCHEMATIC_ONLY"
    assert posture["C_k"] == "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY"
    assert posture["Rep32"] == "NO_CONTINUUM_ACTION_AUTHORITY"
    assert posture["tensor_field_equation"] == "NOT_DERIVED"
    assert posture["gravitomagnetic_recovery"] == "BLOCKED_UPSTREAM"


def test_review_executes_no_action_fork_variation_tooling_or_automation() -> None:
    scope = _report()["scope"]
    assert scope["independent_review_executed"] is True
    assert scope["contract_design_accepted"] is True
    for key, value in scope.items():
        if key not in {"independent_review_executed", "contract_design_accepted"}:
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "no native gravitational principle",
        "Candidate-first work is blocked",
        "Matter coupling remains independently undefined",
        "No action",
        "general tooling",
        "automation",
    ):
        assert token in claim
