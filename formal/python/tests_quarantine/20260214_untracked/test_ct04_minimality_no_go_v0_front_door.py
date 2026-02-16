from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.ct04_minimality_no_go_v0 import (
    CT04MinimalityReport,
    CT04_TOLERANCE_PROFILE_ENV,
    ct04_compare_surfaces,
    ct04_minimality_no_go_v0_record,
    ct04_v0_tolerance_profile_from_env,
    ct04_v0_tolerances,
)
from formal.python.tools.ct04_minimality_no_go_front_door import build_ct04_reports


def _write_ct04_report(path: Path, report: CT04MinimalityReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> CT04MinimalityReport:
    report, _ = build_ct04_reports()
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return CT04MinimalityReport(
        schema=payload["schema"],
        config_tag=payload["config_tag"],
        regime_tag=payload["regime_tag"],
        domain_tag=payload["domain_tag"],
        params={k: float(v) for k, v in payload["params"].items()},
        boundary=str(payload["boundary"]),
        cases=[
            type(report.cases[0])(
                case_id=str(case["case_id"]),
                kind=str(case["kind"]),
                constraint_mode=str(case["constraint_mode"]),
                dt=float(case["dt"]),
                steps=int(case["steps"]),
                cfl=float(case["cfl"]),
                rel_drift=float(case["rel_drift"]),
                max_rel_drift=float(case["max_rel_drift"]),
            )
            for case in payload["cases"]
        ],
    )


def test_ct04_record_is_deterministic_and_schema_stable():
    rec1 = ct04_minimality_no_go_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = ct04_minimality_no_go_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "CT-04_minimality_no_go_comparator/v0"
    assert rec1.observable_id == "CT-04"
    assert rec1.domain_id == "CT-DOMAIN-04"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_ct04_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert ct04_v0_tolerance_profile_from_env({}) == "pinned"
    assert ct04_v0_tolerance_profile_from_env({CT04_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="ct04-prof-ref", regime_tag="ct04-minimality")
    cand = _make_report(config_tag="ct04-prof-cand", regime_tag="ct04-minimality")
    _write_ct04_report(tmp_path / "ct04_reference_report.json", ref)
    _write_ct04_report(tmp_path / "ct04_candidate_report.json", cand)

    rec = ct04_minimality_no_go_v0_record(
        date="2026-02-09",
        env={CT04_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_ct04_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        ct04_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "CT-04/minimality_no_go_front_door_report/v1"},
            {"schema": "CT-04/minimality_no_go_front_door_report/v1"},
            tolerances=ct04_v0_tolerances("pinned"),
        )


def test_ct04_controls_pass():
    report = _make_report(config_tag="ct04-ref", regime_tag="ct04-minimality")
    rows = ct04_compare_surfaces(report, report, tolerances=ct04_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_ct04_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="ct04-neg-fp-ref", regime_tag="ct04-minimality")
    cand = _make_report(config_tag="ct04-neg-fp-cand", regime_tag="ct04-minimality")
    _write_ct04_report(tmp_path / "ct04_reference_report.json", ref)
    _write_ct04_report(tmp_path / "ct04_candidate_report.json", cand, tamper_fingerprint=True)

    rec = ct04_minimality_no_go_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_ct04_blocks_when_artifacts_missing(tmp_path: Path):
    rec = ct04_minimality_no_go_v0_record(
        date="2026-02-09",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
