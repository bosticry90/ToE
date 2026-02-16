from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.ct05_rep_invariant_admissibility_class_v0 import (
    CT05RepInvariantReport,
    CT05_TOLERANCE_PROFILE_ENV,
    ct05_compare_surfaces,
    ct05_rep_invariant_admissibility_class_v0_record,
    ct05_v0_tolerance_profile_from_env,
    ct05_v0_tolerances,
)
from formal.python.tools.ct05_rep_invariant_admissibility_class_front_door import build_ct05_reports


def _write_ct05_report(path: Path, report: CT05RepInvariantReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> CT05RepInvariantReport:
    report, _ = build_ct05_reports()
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return CT05RepInvariantReport(
        schema=payload["schema"],
        config_tag=payload["config_tag"],
        regime_tag=payload["regime_tag"],
        domain_tag=payload["domain_tag"],
        params={k: payload["params"][k] for k in payload["params"]},
        boundary=str(payload["boundary"]),
        cases=[
            type(report.cases[0])(
                case_id=str(case["case_id"]),
                kind=str(case["kind"]),
                admissible_ref=bool(case["admissible_ref"]),
                admissible_rep=bool(case["admissible_rep"]),
                bound_ok_ref=bool(case["bound_ok_ref"]),
                bound_ok_rep=bool(case["bound_ok_rep"]),
                bound_residual=float(case["bound_residual"]),
                rep_delta=float(case["rep_delta"]),
            )
            for case in payload["cases"]
        ],
    )


def test_ct05_record_is_deterministic_and_schema_stable():
    rec1 = ct05_rep_invariant_admissibility_class_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = ct05_rep_invariant_admissibility_class_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "CT-05_rep_invariant_admissibility_class_comparator/v0"
    assert rec1.observable_id == "CT-05"
    assert rec1.domain_id == "CT-DOMAIN-05"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_ct05_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert ct05_v0_tolerance_profile_from_env({}) == "pinned"
    assert ct05_v0_tolerance_profile_from_env({CT05_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="ct05-prof-ref", regime_tag="ct05-rep-invariant")
    cand = _make_report(config_tag="ct05-prof-cand", regime_tag="ct05-rep-invariant")
    _write_ct05_report(tmp_path / "ct05_reference_report.json", ref)
    _write_ct05_report(tmp_path / "ct05_candidate_report.json", cand)

    rec = ct05_rep_invariant_admissibility_class_v0_record(
        date="2026-02-09",
        env={CT05_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_ct05_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        ct05_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1"},
            {"schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1"},
            tolerances=ct05_v0_tolerances("pinned"),
        )


def test_ct05_controls_pass():
    report = _make_report(config_tag="ct05-ref", regime_tag="ct05-rep-invariant")
    rows = ct05_compare_surfaces(report, report, tolerances=ct05_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"].startswith("negative_control")]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 2
    assert pos_rows[0]["passed"] is True
    assert all(row["passed"] for row in neg_rows)


def test_ct05_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="ct05-neg-fp-ref", regime_tag="ct05-rep-invariant")
    cand = _make_report(config_tag="ct05-neg-fp-cand", regime_tag="ct05-rep-invariant")
    _write_ct05_report(tmp_path / "ct05_reference_report.json", ref)
    _write_ct05_report(tmp_path / "ct05_candidate_report.json", cand, tamper_fingerprint=True)

    rec = ct05_rep_invariant_admissibility_class_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_ct05_blocks_when_artifacts_missing(tmp_path: Path):
    rec = ct05_rep_invariant_admissibility_class_v0_record(
        date="2026-02-09",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
