from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    assert packet.artifact_bytes() == packet.artifact_bytes() == REPORT_PATH.read_bytes()


def test_packet_preserves_every_frozen_authority_and_source_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    packet.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == packet.AUTHORITY_AND_SOURCE_HASHES


def test_packet_consumes_selected_target_and_stops_for_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "INDEPENDENT_AUTHORITY_RECONCILIATION_REVIEW_ONLY"
    )
    assert report["hard_stop"]["only_independent_review_next"] is True
    assert report["hard_stop"]["precedence_ruling_authorized_now"] is False


def test_original_action_binding_is_exact_and_chronology_is_not_authority() -> None:
    action = _report()["original_action"]
    assert action["source_id"] == "TOE_CANDIDATE_MASTER_ACTION_v0"
    assert action["authority_class"] == "P_POLICY_WORKING_FORM_NONCANONICAL_UNPROMOTED"
    assert action["internal_captured_date"] == "NOT_DECLARED"
    assert action["displayed_term"] == "sum_k lambda_k C_k(g,psi,A,phi,rho)"
    assert action["complete_C_k_and_lambda_dynamical_contract_supplied"] is False
    assert action["repository_history_is_precedence_authority"] is False


def test_eleven_controlling_firewall_sources_are_bound_with_scope() -> None:
    corpus = _report()["firewall_corpus"]
    assert corpus["controlling_source_count"] == len(corpus["rows"]) == 11
    assert corpus["rows"] == packet.FIREWALL_SOURCES
    assert corpus["unreviewed_preparation_packets_are_independent_controlling_authority"] is False
    scopes = {row["scope"] for row in corpus["rows"]}
    assert "AGGREGATE_CK_FAMILY_STATUS" in scopes
    assert "AGGREGATE_MASTER_ACTION_SELECTOR" in scopes
    assert "PSI_A_EXCHANGE_LANE" in scopes


def test_explicit_supersession_scan_is_reproducible_but_not_a_ruling() -> None:
    scan = _report()["explicit_token_scan"]
    assert scan["classification"] == "PREPARATION_SCAN_NOT_PRECEDENCE_RULING"
    assert scan["patterns"] == packet.SUPERSESSION_PATTERNS
    assert scan["source_count"] == 11
    assert scan["total_match_count"] == 0
    assert scan["preparation_finding"] == (
        "NO_EXPLICIT_SUPERSESSION_TOKEN_FOUND_IN_PREPARATION_SCAN"
    )
    assert all(row["match_count"] == 0 and row["matches"] == {} for row in scan["rows"])


def test_four_existing_authority_rules_are_bound_without_last_write_wins() -> None:
    rules = _report()["existing_authority_rules"]
    assert rules["rule_count"] == len(rules["rows"]) == 4
    assert rules["rows"] == packet.AUTHORITY_RULES
    assert rules["general_later_timestamp_wins_rule_bound"] is False
    assert rules["new_precedence_rule_may_be_invented_by_review"] is False


def test_precedence_hierarchy_and_insufficient_evidence_are_explicit() -> None:
    report = _report()
    assert len(report["precedence_evidence_hierarchy"]) == 4
    assert len(report["insufficient_evidence_alone"]) == 7
    assert "later date" in report["insufficient_evidence_alone"]
    assert "lambda_k=0 workaround" in report["insufficient_evidence_alone"]


def test_resolution_contract_has_four_exact_outcomes() -> None:
    contract = _report()["resolution_contract"]
    assert contract["exactly_one_terminal_outcome_required"] is True
    assert contract["allowed_outcomes"] == packet.ALLOWED_OUTCOMES
    assert len(contract["rows"]) == 4
    assert contract["rows"][0]["maximum_next_authority"] == (
        "prepare_TOE_CANDIDATE_MASTER_ACTION_v1_without_Ck_dynamics"
    )


def test_historical_v0_and_possible_successor_boundaries_are_strict() -> None:
    boundary = _report()["historical_and_successor_boundaries"]
    assert boundary["historical_v0_byte_preserved"] is True
    assert boundary["v0_may_be_silently_modified"] is False
    assert boundary["lambda_k_zero_is_resolution"] is False
    assert boundary["C_k_may_be_declared_inactive_inside_v0"] is False
    assert boundary["successor_created_by_packet"] is False
    assert boundary["possible_successor_initial_classification"] == (
        "WORKING_FORM_NONCANONICAL_UNPROMOTED_UNVARIED"
    )


def test_all_downstream_variational_and_gr_gates_remain_closed() -> None:
    downstream = _report()["downstream_gates"]
    assert downstream["tetrad_and_spin_connection"] == "CLOSED_NOT_EVALUATED"
    assert downstream["stress_energy_generation"] == "CLOSED_NOT_EVALUATED"
    assert downstream["Rep32_relationship"] == "CLOSED_NOT_EVALUATED"
    assert downstream["tensor_field_equation"] == "CLOSED_NOT_DERIVED"
    assert downstream["gravitomagnetic_recovery"] == (
        "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE"
    )


def test_packet_executes_no_ruling_mutation_variation_or_automation() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_only"] is True
    for key, value in scope.items():
        if key != "packet_preparation_only":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No precedence decision",
        "action mutation",
        "successor action",
        "C_k dynamics",
        "variation",
        "automation",
    ):
        assert token in claim
