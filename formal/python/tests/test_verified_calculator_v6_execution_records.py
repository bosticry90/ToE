from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from formal.python.toe.generic_runner.verified_calculator.canonical import digest
from formal.python.tools.generate_vpc_v6_execution_records import (
    MISMATCH_REPORT,
    RUN_LOG,
    build_mismatch_report,
    build_run_log,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def _stored(path: Path) -> dict:
    return json.loads((REPO_ROOT / path).read_text(encoding="utf-8"))


def test_v6_payload_mismatch_inventory_is_complete_and_not_run() -> None:
    report = build_mismatch_report(REPO_ROOT)
    assert report == _stored(MISMATCH_REPORT)
    assert report["status"] == "NOT_RUN"
    assert report["final_disposition"] == "NOT_RUN"
    assert report["required_row_count"] == len(report["rows"]) == 643
    assert len({row["row_id"] for row in report["rows"]}) == 643
    assert Counter(row["disposition"] for row in report["rows"]) == {"NOT_RUN": 643}
    assert report["surface_counts"] == {
        "PE-00-SCOPE-AND-MODEL-CONVENTIONS": 1,
        "PE-01-SOURCES": 31,
        "PE-02-DERIVED-GRAPH": 160,
        "PE-03-TRUSTED-OPERATION-VOCABULARY": 19,
        "PE-04-AUTHORITATIVE-ROOTS": 16,
        "PE-05-CHALLENGE-SPECIFICATIONS": 10,
        "PE-06-CHALLENGE-INSTANCES-AND-RESULTS": 373,
        "PE-07-CLAIM-LEDGER": 16,
        "PE-08-SCIENTIFIC-AUTHORITY": 16,
        "PE-09-NON-PROMOTION-AND-EXACT-SCOPE": 1,
    }
    claimed = report.pop("report_hash")
    assert digest(report, domain=report["schema_id"]) == claimed


def test_v6_execution_run_log_has_every_check_and_no_claimed_result() -> None:
    log = build_run_log(REPO_ROOT)
    assert log == _stored(RUN_LOG)
    assert log["status"] == "NOT_RUN"
    assert log["final_disposition"] == "NOT_RUN"
    assert log["required_check_count"] == len(log["checks"]) == 104
    assert [row["check_id"] for row in log["checks"]] == [f"V6-RUN-{index:03d}" for index in range(1, 105)]
    assert all(row["mandatory"] and row["status"] == "NOT_RUN" for row in log["checks"])
    assert log["summary"] == {"NOT_RUN": 104, "PASS": 0, "FAIL": 0, "INCONCLUSIVE": 0, "BLOCKED": 0}
    assert log["scientific_promotion"] is False
    assert log["product_v1_release"] is False
    assert log["production_activation"] is False
    claimed = log.pop("run_log_hash")
    assert digest(log, domain=log["schema_id"]) == claimed
