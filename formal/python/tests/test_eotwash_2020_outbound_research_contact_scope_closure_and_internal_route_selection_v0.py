from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    eotwash_2020_outbound_research_contact_scope_closure_and_internal_route_selection_v0
    as closure,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / closure.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_closure_regenerates_and_consumes_exact_live_authority() -> None:
    assert closure.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == closure.TARGET
    assert report["verdict"] == closure.VERDICT
    assert report["consumed_target"] == closure.CONSUMED_TARGET
    assert report["selected_next_target"] == closure.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_prior_selector_artifacts"]
    } == closure.AUTHORITY_HASHES


def test_explicit_user_scope_withdraws_contact_without_rewriting_science() -> None:
    report = _report()
    assert report["selection_basis"] == "EXPLICIT_USER_SCOPE_OVERRIDE"
    assert report["historical_selector"]["scientific_ranking_retracted"] is False
    assert report["historical_selector"]["live_contact_route_withdrawn"] is True
    posture = report["retained_empirical_posture"]
    assert posture["experiment_suitable"] is True
    assert posture["evidence_components_complete"] == 0
    assert posture["evidence_component_count"] == 6
    assert posture["independent_likelihood_executable"] is False


def test_durable_internal_research_policy_is_exact() -> None:
    policy = _report()["standing_internal_research_policy"]
    assert policy == {
        "outbound_research_contact": "DISALLOWED_UNLESS_USER_EXPLICITLY_REOPENS",
        "dependence_on_private_or_restricted_data": "DISALLOWED",
        "waiting_on_third_party_cooperation": "DISALLOWED",
        "public_papers_and_openly_available_data": "PERMITTED",
        "internal_theory_simulation_and_synthetic_testing": "PERMITTED",
        "reopening_authority": "EXPLICIT_FUTURE_USER_INSTRUCTION_ONLY",
    }


def test_no_contact_artifact_or_communication_was_created() -> None:
    scope = _report()["scope"]
    assert scope["contact_preparation_withdrawn"] is True
    assert scope["outbound_research_contact_disallowed"] is True
    assert scope["contact_packet_prepared"] is False
    assert scope["contact_recipient_selected"] is False
    assert scope["contact_message_drafted"] is False
    assert scope["author_or_custodian_contact_authorized"] is False
    assert scope["author_or_custodian_contact_executed"] is False


def test_eotwash_independent_fit_is_closed_without_empirical_inference() -> None:
    posture = _report()["retained_empirical_posture"]
    assert posture["independent_fit_route"] == "CLOSED_BLOCKED_ON_INACCESSIBLE_INPUTS"
    assert posture["likelihood"] == "NOT_EXECUTED"
    assert posture["scalar_range_bound"] == "NONE"
    assert posture["alpha_constraint"] == "NONE"


def test_synthetic_route_is_packet_preparation_only() -> None:
    route = _report()["selected_internal_route"]
    assert route["candidate_id"] == (
        "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST"
    )
    assert route["target"] == closure.SELECTED_NEXT_TARGET
    assert route["status"] == "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED"
    assert route["classification"] == (
        "SYNTHETIC_FORECAST_NOT_EOTWASH_EMPIRICAL_REANALYSIS_NOT_MEASURED_CONSTRAINT"
    )
    scope = _report()["scope"]
    assert scope["synthetic_packet_preparation_authorized"] is True
    assert scope["synthetic_forecast_executed"] is False


def test_published_reinterpretation_is_not_authorized() -> None:
    route = _report()["deferred_public_evidence_route"]
    assert route["status"] == "NOT_AUTHORIZED"
    assert route["claim_classification_if_later_authorized"] == (
        "SUPPLIED_PUBLISHED_CONSTRAINT_NOT_INDEPENDENTLY_REPRODUCED"
    )


def test_all_sixteen_closure_gates_pass() -> None:
    gates = _report()["closure_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 16
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_contains_no_analysis_bound_or_adoption() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "scope_closure_executed",
        "explicit_user_scope_override",
        "contact_preparation_withdrawn",
        "outbound_research_contact_disallowed",
        "private_restricted_data_dependence_disallowed",
        "third_party_waiting_disallowed",
        "public_open_evidence_permitted",
        "internal_synthetic_research_permitted",
        "explicit_user_reopening_required",
        "eotwash_independent_fit_route_closed",
        "synthetic_packet_preparation_authorized",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_and_policy_surfaces_preserve_claim_boundaries() -> None:
    human = (REPO_ROOT / closure.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    policy = (REPO_ROOT / closure.POLICY_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "WITHDRAWN BY USER SCOPE",
        "PROHIBITED UNTIL EXPLICITLY REOPENED",
        closure.SELECTED_NEXT_TARGET,
        "NOT AUTHORIZED",
    ):
        assert token in human
    for token in (
        "DISALLOWED UNLESS THE USER EXPLICITLY REOPENS IT",
        "DEPENDENCE ON PRIVATE OR RESTRICTED DATA",
        "INTERNAL THEORY, SIMULATION, AND SYNTHETIC TESTING",
        "SYNTHETIC FORECAST",
    ):
        assert token in policy

