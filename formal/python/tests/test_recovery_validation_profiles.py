from __future__ import annotations

from formal.python.tools import recovery_validation_profiles as subject


def _outcome(nodeid: str, order: int, family: str, root: str) -> dict:
    return {
        "nodeid": nodeid,
        "order_index": order,
        "root_family": family,
        "root_id": root,
        "first_exception": "synthetic",
    }


def test_profiles_partition_collection_and_never_demote_a_current_test() -> None:
    current = [
        (
            "formal/python/tests/test_recovery_validation_profiles.py::"
            "test_profiles_partition_collection_and_never_demote_a_current_test"
        ),
        "formal/python/tests/test_historical_example.py::test_old",
    ]
    historical_outcomes = [
        _outcome(
            f"formal/python/tests/test_placeholder_{index}.py::test_case",
            index,
            "missing_artifacts",
            f"MISSING::{index}",
        )
        for index in range(1, 370)
    ]
    frozen = [current[1], *[row["nodeid"] for row in historical_outcomes]]
    outcomes = {
        "entries": [
            *historical_outcomes,
            _outcome(current[1], 370, "missing_artifacts", "MISSING::370"),
        ]
    }
    missing = {
        "expectation_rows": [
            {
                "outcome_nodeid": row["nodeid"],
                "authority_classification": "HISTORICAL_REPORT_BEYOND_RETENTION",
            }
            for row in outcomes["entries"]
        ]
    }
    profiles = subject.build_profiles(
        repo_root=subject.REPO_ROOT,
        current_nodeids=[
            *current,
            *[row["nodeid"] for row in outcomes["entries"][:-1]],
        ],
        frozen_nodeids=frozen,
        outcome_ledger=outcomes,
        missing_ledger=missing,
        cluster_ledger={"custody_currency_outcomes": {"nodeids": []}},
        relative_to_commit="0" * 40,
    )
    current_ids = set(profiles["current"]["nodeids"])
    historical_ids = set(profiles["historical"]["nodeids"])
    assert current_ids.isdisjoint(historical_ids)
    assert current_ids | historical_ids == set(
        profiles["current"]["nodeids"] + profiles["historical"]["nodeids"]
    )
    assert current[0] in current_ids
    assert profiles["reconciliation"]["exact_partition"] is True


def test_missing_provenance_block_can_be_quarantined_only_when_noncurrent() -> None:
    row = _outcome(
        "formal/python/tests/test_historical_example.py::test_old",
        1,
        "missing_artifacts",
        "MISSING::one",
    )
    axes = subject._nonpassing_axes(
        row,
        reachable_criticality=[],
        reachability_evidence=[],
        missing_row={"authority_classification": "PROVENANCE_INCOMPLETE"},
        unratified=False,
    )
    assert axes["criticality"] == ["NONCURRENT"]
    assert axes["provenance"] == "BLOCKED"
    assert axes["disposition"] == "QUARANTINED"
    assert axes["current_reachability_unknown"] is False


def test_unknown_nonpassing_reachability_fails_closed_into_current_profile() -> None:
    row = _outcome(
        "formal/python/tests/test_unknown.py::test_unknown",
        1,
        "other_packet_contract",
        "PACKET::unknown",
    )
    axes = subject._nonpassing_axes(
        row,
        reachable_criticality=[],
        reachability_evidence=[],
        missing_row=None,
        unratified=False,
    )
    assert axes["criticality"] == ["CURRENT_REPRODUCIBILITY"]
    assert axes["disposition"] == "BLOCKING"
    assert axes["current_reachability_unknown"] is True
