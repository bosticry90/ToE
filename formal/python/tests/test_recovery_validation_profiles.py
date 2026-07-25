from __future__ import annotations

from pathlib import Path

from formal.python.tools import recovery_profile_runner
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
    generated = recovery_profile_runner.freeze_profile_state()
    assert len(generated) == 4
    assert all(len(value) == 64 for value in generated.values())
    current_generated = recovery_profile_runner.load_profile(
        "current_control_plane"
    )
    historical_generated = recovery_profile_runner.load_profile("historical_debt")
    assert set(current_generated["nodeids"]).isdisjoint(
        historical_generated["nodeids"]
    )
    assert current_generated["nodeid_count"] + historical_generated[
        "nodeid_count"
    ] == current_generated["inventory_count"]
    result = subject.load_json(
        subject.REPO_ROOT
        / "formal/docs/release/"
        "RECOVERY_OBLIGATION_PROFILE_CONSTRUCTION_RESULT_20260725_v0.json"
    )
    assert result["artifacts"]["current_control_plane"]["nodeids"] == 3748
    assert result["artifacts"]["historical_debt"]["nodeids"] == 10078
    assert result["classification"]["unknown_current_reachability_obligations"] == 102
    assert result["terminal_outcome"] == "RECOVERY_BLOCKED_CURRENT_PROFILE_COVERAGE"
    assert result["authorization"]["successor_authority"] == "NONE"
    review = subject.load_json(
        subject.REPO_ROOT
        / "formal/docs/release/"
        "RECOVERY_OBLIGATION_PROFILE_CONSTRUCTION_RESULT_REVIEW_20260725_v0.json"
    )
    assert review["accepted"] is True
    assert review["findings"]["exact_profile_partition"] is True
    assert review["accepted_terminal_outcome"] == (
        "RECOVERY_BLOCKED_CURRENT_PROFILE_COVERAGE"
    )
    assert review["successor_authority"] == "NONE"
    registry_v1 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "RECOVERY_OBLIGATION_REGISTRY_20260725_v1.json"
    )
    current_v1 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "CURRENT_CONTROL_PLANE_PROFILE_20260725_v1.json"
    )
    historical_v1 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "HISTORICAL_DEBT_PROFILE_20260725_v1.json"
    )
    reconciliation_v1 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "VALIDATION_PROFILE_RECONCILIATION_20260725_v1.json"
    )
    nonpassing_v1 = [
        row
        for row in registry_v1["obligations"]
        if row["obligation_id"].startswith("NONPASSING-")
    ]
    assert len(nonpassing_v1) == 357
    assert current_v1["known_nonpassing_count"] == 4
    assert historical_v1["known_nonpassing_count"] == 353
    assert reconciliation_v1["unknown_current_reachability_obligations"] == 0
    assert reconciliation_v1["exact_partition"] is True
    assert current_v1["nodeid_count"] + historical_v1["nodeid_count"] == 13838
    result_v1 = subject.load_json(
        subject.REPO_ROOT
        / "formal/docs/release/"
        "RECOVERY_VALIDATION_PROFILE_V1_IMPLEMENTATION_RESULT_20260725_v0.json"
    )
    assert result_v1["profile_artifacts"]["current_control_plane"][
        "known_nonpassing"
    ] == 4
    assert result_v1["profile_artifacts"]["historical_debt"][
        "known_nonpassing"
    ] == 353
    assert result_v1["current_acceptance_inventory"]["count"] == 13838
    assert result_v1["terminal_outcome"] == (
        "RECOVERY_VALIDATION_PROFILE_V1_IMPLEMENTED_FOUR_CURRENT_REPAIRS_REMAIN"
    )
    review_v1 = subject.load_json(
        subject.REPO_ROOT
        / "formal/docs/release/"
        "RECOVERY_VALIDATION_PROFILE_V1_IMPLEMENTATION_RESULT_REVIEW_20260725_v0.json"
    )
    assert review_v1["accepted"] is True
    assert review_v1["findings"]["current_known_nonpassing"] == 4
    assert review_v1["findings"]["unknown_current_reachability"] == 0
    assert review_v1["findings"]["historical_isolation_still_unproven"] is True
    assert review_v1["successor_authority"] == "NONE"
    registry_v2 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "RECOVERY_OBLIGATION_REGISTRY_20260725_v2.json"
    )
    current_v2 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "CURRENT_CONTROL_PLANE_PROFILE_20260725_v2.json"
    )
    historical_v2 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "HISTORICAL_DEBT_PROFILE_20260725_v2.json"
    )
    reconciliation_v2 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "VALIDATION_PROFILE_RECONCILIATION_20260725_v2.json"
    )
    nonpassing_v2 = [
        row
        for row in registry_v2["obligations"]
        if row["obligation_id"].startswith("NONPASSING-")
    ]
    assert len(nonpassing_v2) == 354
    assert current_v2["known_nonpassing_count"] == 0
    assert historical_v2["known_nonpassing_count"] == 354
    assert reconciliation_v2["unknown_current_reachability_obligations"] == 0
    assert reconciliation_v2["exact_partition"] is True
    assert current_v2["nodeid_count"] + historical_v2["nodeid_count"] == 13838
    repaired_current = {
        (
            "formal/python/tests/test_admissibility_manifest.py::"
            "test_admissibility_manifest_exists_and_matches_current"
        ),
        (
            "formal/python/tests/test_admissibility_manifest.py::"
            "test_admissibility_manifest_tracks_lean_gate_stubs_deterministically"
        ),
        (
            "formal/python/tests/"
            "test_formal_docs_paper_cross_reference_integrity_gate.py::"
            "test_formal_docs_paper_and_state_cross_references_resolve"
        ),
    }
    historical_eol = (
        "formal/python/tests/test_repository_canonical_text_integrity_gate.py::"
        "test_eol_policy_does_not_glob_hash_bound_historical_trees"
    )
    assert repaired_current <= set(current_v2["nodeids"])
    assert historical_eol in set(historical_v2["nodeids"])
    assert historical_eol not in set(current_v2["nodeids"])
    registry_v3 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "RECOVERY_OBLIGATION_REGISTRY_20260725_v3.json"
    )
    current_v3 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "CURRENT_CONTROL_PLANE_PROFILE_20260725_v3.json"
    )
    historical_v3 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "HISTORICAL_DEBT_PROFILE_20260725_v3.json"
    )
    reconciliation_v3 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "VALIDATION_PROFILE_RECONCILIATION_20260725_v3.json"
    )
    nonpassing_v3 = [
        row
        for row in registry_v3["obligations"]
        if row["obligation_id"].startswith("NONPASSING-")
    ]
    assert len(nonpassing_v3) == 354
    assert current_v3["known_nonpassing_count"] == 0
    assert historical_v3["known_nonpassing_count"] == 354
    assert reconciliation_v3["unknown_current_reachability_obligations"] == 0
    assert reconciliation_v3["exact_partition"] is True
    assert current_v3["nodeid_count"] + historical_v3["nodeid_count"] == 13838
    assert repaired_current <= set(current_v3["nodeids"])
    assert historical_eol in set(historical_v3["nodeids"])
    assert historical_eol not in set(current_v3["nodeids"])
    registry_v4 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "RECOVERY_OBLIGATION_REGISTRY_20260725_v4.json"
    )
    current_v4 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "CURRENT_CONTROL_PLANE_PROFILE_20260725_v4.json"
    )
    historical_v4 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "HISTORICAL_DEBT_PROFILE_20260725_v4.json"
    )
    reconciliation_v4 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "VALIDATION_PROFILE_RECONCILIATION_20260725_v4.json"
    )
    nonpassing_v4 = [
        row
        for row in registry_v4["obligations"]
        if row["obligation_id"].startswith("NONPASSING-")
    ]
    assert len(nonpassing_v4) == 354
    assert current_v4["known_nonpassing_count"] == 0
    assert historical_v4["known_nonpassing_count"] == 354
    assert reconciliation_v4["unknown_current_reachability_obligations"] == 0
    assert reconciliation_v4["exact_partition"] is True
    assert current_v4["nodeid_count"] + historical_v4["nodeid_count"] == 13838
    assert repaired_current <= set(current_v4["nodeids"])
    assert historical_eol in set(historical_v4["nodeids"])
    assert historical_eol not in set(current_v4["nodeids"])
    registry_v5 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "RECOVERY_OBLIGATION_REGISTRY_20260725_v5.json"
    )
    current_v5 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "CURRENT_CONTROL_PLANE_PROFILE_20260725_v5.json"
    )
    historical_v5 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "HISTORICAL_DEBT_PROFILE_20260725_v5.json"
    )
    reconciliation_v5 = subject.load_json(
        subject.REPO_ROOT
        / "formal/output/validation_profiles/"
        "VALIDATION_PROFILE_RECONCILIATION_20260725_v5.json"
    )
    nonpassing_v5 = [
        row
        for row in registry_v5["obligations"]
        if row["obligation_id"].startswith("NONPASSING-")
    ]
    assert len(nonpassing_v5) == 354
    assert current_v5["known_nonpassing_count"] == 0
    assert historical_v5["known_nonpassing_count"] == 354
    assert reconciliation_v5["unknown_current_reachability_obligations"] == 0
    assert reconciliation_v5["exact_partition"] is True
    assert current_v5["nodeid_count"] + historical_v5["nodeid_count"] == 13856
    dirty_custody_guards = {
        nodeid
        for nodeid in current_v5["nodeids"]
        if (
            "test_repository_dirty_main_terminal_custody_disposition_v0.py"
            in nodeid
        )
    }
    assert len(dirty_custody_guards) == 12
    assert repaired_current <= set(current_v5["nodeids"])
    assert historical_eol in set(historical_v5["nodeids"])
    assert historical_eol not in set(current_v5["nodeids"])


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


def test_historical_junit_accepts_only_recorded_nonpassing(tmp_path: Path) -> None:
    nodeid = "formal/python/tests/test_old.py::TestOld::test_recorded"
    junit = tmp_path / "historical.xml"
    junit.write_text(
        '<testsuites><testsuite tests="1" failures="1" errors="0">'
        '<testcase classname="formal.python.tests.test_old.TestOld" '
        'name="test_recorded"><failure>expected</failure></testcase>'
        "</testsuite></testsuites>",
        encoding="utf-8",
    )
    result = recovery_profile_runner.reconcile_historical_junit(
        profile={
            "profile": "historical_debt",
            "nodeid_count": 1,
            "nodeids": [nodeid],
            "known_nonpassing_nodeids": [nodeid],
        },
        junit_path=junit,
        pytest_exit_code=1,
    )
    assert result["accepted"] is True
    assert result["unexpected_nonpassing"] == []
    assert result["verdict"] == (
        "HISTORICAL_DEBT_COMPLETE_WITH_RECORDED_FAILURES"
    )
