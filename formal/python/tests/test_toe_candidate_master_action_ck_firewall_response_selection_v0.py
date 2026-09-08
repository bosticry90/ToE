from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import toe_candidate_master_action_ck_firewall_response_selection_v0 as selection


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_exactly_and_deterministically() -> None:
    assert selection.artifact_bytes() == selection.artifact_bytes() == REPORT_PATH.read_bytes()


def test_selection_preserves_every_frozen_authority_byte() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_selection_consumes_terminal_contract_block_response_target() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == "SELECTED_CK_FIREWALL_AUTHORITY_RECONCILIATION_PREPARATION"
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "PREPARATION_ONLY_MASTER_ACTION_AUTHORITY_RECONCILIATION"
    )


def test_firewall_reconciliation_ranks_first() -> None:
    ranking = _report()["ranking"]
    assert len(ranking["rows"]) == 4
    assert ranking["selected_candidate_id"] == (
        "PRESERVE_CK_FIREWALL_AND_RECONCILE_MASTER_ACTION_AUTHORITY"
    )
    assert ranking["selected_score"] == 97
    assert ranking["runner_up_candidate_id"] == "CLASSIFY_MASTER_ACTION_SCHEMATIC_ONLY"
    assert ranking["runner_up_score"] == 88


def test_selection_is_stable_under_all_twenty_four_weight_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == (
            "PRESERVE_CK_FIREWALL_AND_RECONCILE_MASTER_ACTION_AUTHORITY"
        )
        for row in sensitivity["rows"]
    )


def test_selected_packet_freezes_chronology_without_assuming_date_precedence() -> None:
    obligation = _report()["selected_scientific_obligation"]
    assert obligation["obligation_class"] == (
        "AUTHORITY_CHRONOLOGY_AND_PRECEDENCE_RECONCILIATION"
    )
    assert len(obligation["packet_must_freeze"]) == 7
    joined = "\n".join(obligation["packet_must_freeze"])
    for token in (
        "original candidate action",
        "later accepted C_k",
        "without assuming later-date precedence",
        "explicitly supersedes, amends, or merely conflicts",
        "no claim inheritance",
        "downstream tetrad",
    ):
        assert token in joined


def test_four_exact_terminal_results_are_allowed() -> None:
    outcomes = _report()["selected_scientific_obligation"]["allowed_terminal_results"]
    assert outcomes == [
        "CK_FIREWALL_SUPERSEDES_ACTION_TERM",
        "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
        "CK_DYNAMICAL_EMBEDDING_REQUIRES_NEW_THEORY_SELECTION",
        "BLOCKED_AUTHORITY_PRECEDENCE_UNRESOLVED",
    ]


def test_possible_successor_inherits_no_claims() -> None:
    obligation = _report()["selected_scientific_obligation"]
    assert obligation["possible_successor_classification"] == (
        "WORKING_FORM_NONCANONICAL_UNPROMOTED_UNVARIED"
    )
    assert "do not rewrite v0" in obligation["stopping_rule"]
    assert "create a successor action" in obligation["stopping_rule"]


def test_downstream_scientific_gates_remain_closed() -> None:
    retained = _report()["retained_boundaries"]
    assert retained["native_continuum_action_contract"] == (
        "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT"
    )
    assert retained["tetrad_spinor_surface"] == "NOT_EVALUATED"
    assert retained["stress_energy_generation"] == "NOT_EVALUATED"
    assert retained["Rep32_transport"] == "NOT_EVALUATED"
    assert retained["GR_gravitomagnetic_recovery"] == (
        "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE"
    )


def test_selection_executes_no_reconciliation_rewrite_or_variation() -> None:
    scope = _report()["scope"]
    assert scope["response_selection_executed"] is True
    assert scope["packet_preparation_authorized"] is True
    for key, value in scope.items():
        if key not in {"response_selection_executed", "packet_preparation_authorized"}:
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "no precedence ruling",
        "action rewrite",
        "successor action",
        "C_k dynamics",
        "metric/tetrad variation",
        "automation",
    ):
        assert token in claim
