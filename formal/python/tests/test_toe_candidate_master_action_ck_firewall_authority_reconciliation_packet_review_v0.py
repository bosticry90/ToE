from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_review_v0 as review,
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


def test_review_consumes_packet_and_selects_exactly_one_terminal_outcome() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY"
    assert report["primary_diagnostic"] == (
        "NO_EXECUTABLE_NATIVE_CONTINUUM_ACTION_AUTHORITY"
    )
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "FRESH_SCIENTIFIC_TARGET_SELECTION_ONLY"
    )


def test_source_scope_is_one_eleven_four_with_local_aggregate_split() -> None:
    scope = _report()["source_scope_review"]
    assert scope["status"] == "PASS"
    assert scope["historical_action_source_count"] == 1
    assert scope["firewall_source_count"] == 11
    assert scope["local_or_option_index_source_count"] == 8
    assert scope["aggregate_source_count"] == 3
    assert scope["authority_rule_count"] == 4
    assert scope["chronology_used_as_precedence"] is False
    assert scope["downstream_scientific_convenience_used"] is False


def test_explicit_supersession_is_not_established() -> None:
    supersession = _report()["explicit_supersession_review"]
    assert supersession["status"] == "NOT_ESTABLISHED"
    assert supersession["reproduced_scan_match_count"] == 0
    for key, value in supersession.items():
        if key not in {"status", "reproduced_scan_match_count"}:
            assert value is False, key


def test_historical_action_is_preserved_and_not_silently_reinterpreted() -> None:
    action = _report()["historical_action_review"]
    assert action["classification"] == (
        "P_POLICY_WORKING_FORM_NONCANONICAL_UNPROMOTED"
    )
    assert action["working_form_only_self_classification"] is True
    assert action["contains_displayed_C_k_multiplier_term"] is True
    assert action["contains_stationarity_condition"] is True
    assert action["complete_C_k_multiplier_variation_contract"] is False
    assert action["historical_bytes_preserved"] is True
    assert action["term_deleted_declared_inactive_or_projected"] is False


def test_three_aggregate_sources_establish_organizing_surface_ceiling() -> None:
    aggregate = _report()["aggregate_organizing_surface_review"]
    assert aggregate["status"] == "PASS"
    assert aggregate["source_count"] == len(aggregate["rows"]) == 3
    assert aggregate["rows"] == review.AGGREGATE_SOURCES
    assert aggregate["all_C_k_families_admissibility_only"] is True
    assert aggregate["action_embedding_or_variation_authorized"] is False
    assert aggregate["master_action_status"] == (
        "WORKING_FORM_NONCANONICAL_NONPROMOTED_ORGANIZING_SURFACE"
    )


def test_four_existing_rules_are_applied_without_invented_precedence() -> None:
    rules = _report()["authority_rule_application"]
    assert rules["rule_count"] == len(rules["rows"]) == 4
    assert rules["rows"] == review.AUTHORITY_RULE_APPLICATIONS
    assert rules["rule_authorizes_historical_mutation"] is False
    assert rules["rule_authorizes_successor_creation"] is False
    assert rules["rule_authorizes_executable_action_claim"] is False


def test_four_outcomes_are_adjudicated_with_only_schematic_selected() -> None:
    adjudication = _report()["outcome_adjudication"]
    assert adjudication["allowed_outcome_count"] == len(adjudication["rows"]) == 4
    assert adjudication["selected_outcome_count"] == 1
    assert adjudication["rows"] == review.OUTCOME_ADJUDICATION
    selected = [row for row in adjudication["rows"] if row["status"] == "SELECTED"]
    assert [row["outcome"] for row in selected] == [
        "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY"
    ]


def test_schematic_outcome_does_not_claim_supersession_or_dynamic_ck() -> None:
    reasoning = _report()["terminal_reasoning"]
    assert reasoning["selected"] == "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY"
    assert "No accepted source" in reasoning["why_not_explicit_supersession"]
    assert "three accepted aggregate records" in reasoning["why_schematic_only"]
    assert "new theory choice" in reasoning["why_not_dynamical_embedding"]
    assert "maximum present status" in reasoning["why_not_unresolved_precedence"]


def test_retained_status_and_all_downstream_gates_are_bounded() -> None:
    report = _report()
    retained = report["retained_status"]
    assert retained["historical_v0"] == (
        "SCHEMATIC_WORKING_FORM_ORGANIZING_SURFACE"
    )
    assert retained["native_executable_continuum_action"] == "NOT_YET_DEFINED"
    assert retained["successor_action"] == "NOT_CREATED_NOT_PREPARED"
    downstream = report["downstream_gates"]
    assert downstream["tensor_field_equation"] == "CLOSED_NOT_DERIVED"
    assert downstream["gravitomagnetic_recovery"] == (
        "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE"
    )
    assert all(
        value == "CLOSED_NOT_EVALUATED"
        for key, value in downstream.items()
        if key not in {"tensor_field_equation", "gravitomagnetic_recovery"}
    )


def test_review_executes_no_mutation_variation_successor_or_automation() -> None:
    scope = _report()["scope"]
    assert scope["independent_review_executed"] is True
    for key, value in scope.items():
        if key != "independent_review_executed":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No existing authority removes the C_k term",
        "no executable native continuum action",
        "No action mutation",
        "variation",
        "automation",
    ):
        assert token in claim
