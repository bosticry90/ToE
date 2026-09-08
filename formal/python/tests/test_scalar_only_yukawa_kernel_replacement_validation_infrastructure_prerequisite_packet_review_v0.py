from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_review_v0 as review


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_exact_packet() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_review_uses_sandbox_not_production_standard() -> None:
    standard = _report()["review_standard"]
    assert standard["tier"] == "NON_PRODUCTION_EXPLORATORY_SANDBOX_ELIGIBILITY"
    assert standard["production_adoption_assurance_required"] is False
    assert standard["scientific_claim_assurance_required"] is False
    assert standard["mechanical_executability_and_isolation_required"] is True


def test_all_nine_narrow_audits_pass() -> None:
    audits = _report()["independent_audits"]
    assert len(audits) == 9
    assert set(audits.values()) == {"PASS"}


def test_capability_contract_is_accepted_at_bounded_threat_model() -> None:
    text = " ".join(_report()["nonblocking_review_notes"])
    assert "ordinary public-call misuse and replay" in text
    assert "malicious arbitrary code with process-memory access" in text
    assert "cross-platform production hardening" in text


def test_ready_is_not_qualification_or_scientific_validation() -> None:
    notes = " ".join(_report()["nonblocking_review_notes"])
    assert "contract-ready" in notes
    assert "not infrastructure-qualified" in notes
    scope = _report()["scope"]
    assert scope["validation_infrastructure_contract_ready"] is True
    assert scope["infrastructure_implementation_authorized"] is False
    assert scope["candidate_kernel_creation_authorized"] is False


def test_exact_forty_eight_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 48
    assert gates["pass_count"] == 48
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_terminal_consequence_is_exactly_two_option_selector() -> None:
    consequence = _report()["terminal_consequence"]
    assert consequence["current_selector_options_exact"] == [
        "AUTHORIZE_ISOLATED_NON_DECISION_BEARING_SANDBOX_IMPLEMENTATION",
        "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
    ]
    assert consequence["packet_repair"] == "PROHIBITED"
    assert consequence["new_prerequisite"] == "PROHIBITED"
    assert consequence["automatic_sandbox_or_replacement"] == "PROHIBITED"
    assert consequence["selector_must_choose_exactly_one_option"] is True


def test_no_implementation_execution_or_downstream_authority() -> None:
    scope = _report()["scope"]
    assert scope["terminal_independent_review_performed"] is True
    assert scope["two_option_selector_authorized"] is True
    for key in (
        "packet_repair_authorized", "prerequisite_to_prerequisite_authorized",
        "infrastructure_implementation_authorized", "infrastructure_implementation_performed",
        "synthetic_fixture_execution_performed", "candidate_kernel_creation_authorized",
        "candidate_kernel_execution_authorized", "production_change_authorized",
        "old_cubature_called", "old_cubature_adjudicated", "stage_a_rerun_authorized",
        "torque_or_dft_authorized", "jacobian_or_identifiability_authorized",
        "stage_b_authorized",
    ):
        assert scope[key] is False


def test_human_review_records_ready_boundary_and_authority() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT, "48 / 48 PASS", "sandbox eligibility",
        "not infrastructure qualification", "two-option selector",
        "No repair packet", "No infrastructure or fixture code was executed",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
