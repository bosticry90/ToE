from __future__ import annotations

from formal.python.tools import recovery_current_reachability_adjudication as subject


def test_every_conservatively_current_obligation_has_a_terminal_reachability() -> None:
    registry = subject.load_json(subject.DEFAULT_REGISTRY)
    roots = subject.load_json(subject.DEFAULT_ROOTS)
    ledger = subject.build_ledger(
        registry=registry,
        roots=roots,
        registry_path=subject.DEFAULT_REGISTRY,
        roots_path=subject.DEFAULT_ROOTS,
    )
    assert ledger["counts"] == {
        "candidate_obligations": 126,
        "current_repair_required": 4,
        "historical_quarantine_candidates": 89,
        "unratified_quarantine_candidates": 33,
        "unknown_current_reachability_after": 0,
    }
    assert len(ledger["rows"]) == 126
    assert len({row["obligation_id"] for row in ledger["rows"]}) == 126
    assert all(
        row["current_reachability"] in {"VERIFIED_PRESENT", "VERIFIED_ABSENT"}
        for row in ledger["rows"]
    )


def test_noncurrent_does_not_erase_provenance_or_reporting() -> None:
    ledger = subject.load_json(subject.DEFAULT_OUTPUT)
    noncurrent = [
        row for row in ledger["rows"] if row["criticality"] == ["NONCURRENT"]
    ]
    assert len(noncurrent) == 122
    assert all(row["provenance"] in {"VERIFIED", "INCOMPLETE", "BLOCKED"} for row in noncurrent)
    assert all(row["disposition"] == "QUARANTINED" for row in noncurrent)
    assert all(
        "FAILURE_REMAINS_VISIBLE_IN_HISTORICAL_PROFILE"
        in row["reachability_evidence"]
        for row in noncurrent
    )
    assert ledger["invariants"]["historical_isolation_still_required"] is True


def test_only_four_current_nonpassing_obligations_remain_after_adjudication() -> None:
    ledger = subject.load_json(subject.DEFAULT_OUTPUT)
    current = [
        row
        for row in ledger["rows"]
        if row["current_reachability"] == "VERIFIED_PRESENT"
    ]
    assert {row["obligation_id"] for row in current} == set(
        subject.CURRENT_OBLIGATION_AXES
    )
    assert all(row["disposition"] == "PENDING_REPAIR" for row in current)
    assert ledger["scientific_posture"] == "B-BLOCKED"
    assert ledger["v2_enrollment"] == "NOT_AUTHORIZED"
