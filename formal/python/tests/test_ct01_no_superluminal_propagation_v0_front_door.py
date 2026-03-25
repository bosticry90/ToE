from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.ct01_no_superluminal_propagation_v0 import (
    CT01PropagationReport,
    CT01_TOLERANCE_PROFILE_ENV,
    ct01_compare_surfaces,
    ct01_no_superluminal_v0_record,
    ct01_v0_tolerance_profile_from_env,
    ct01_v0_tolerances,
)
from formal.python.tools.ct01_no_superluminal_propagation_front_door import build_ct01_reports


def _write_ct01_report(path: Path, report: CT01PropagationReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> CT01PropagationReport:
    report, _ = build_ct01_reports()
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return CT01PropagationReport(
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
                delta_x=float(case["delta_x"]),
                t_cross=float(case["t_cross"]),
                v_emp=float(case["v_emp"]),
                c_cone=float(case["c_cone"]),
                crossed=bool(case["crossed"]),
                update_mode=str(case["update_mode"]),
            )
            for case in payload["cases"]
        ],
    )


def test_ct01_record_is_deterministic_and_schema_stable():
    rec1 = ct01_no_superluminal_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = ct01_no_superluminal_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "CT-01_no_superluminal_propagation_comparator/v0"
    assert rec1.observable_id == "CT-01"
    assert rec1.domain_id == "CT-DOMAIN-01"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_ct01_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert ct01_v0_tolerance_profile_from_env({}) == "pinned"
    assert ct01_v0_tolerance_profile_from_env({CT01_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="ct01-prof-ref", regime_tag="ct01-no-superluminal")
    cand = _make_report(config_tag="ct01-prof-cand", regime_tag="ct01-no-superluminal")
    _write_ct01_report(tmp_path / "ct01_reference_report.json", ref)
    _write_ct01_report(tmp_path / "ct01_candidate_report.json", cand)

    rec = ct01_no_superluminal_v0_record(
        date="2026-02-09",
        env={CT01_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_ct01_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        ct01_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "CT-01/no_superluminal_propagation_front_door_report/v1"},
            {"schema": "CT-01/no_superluminal_propagation_front_door_report/v1"},
            tolerances=ct01_v0_tolerances("pinned"),
        )


def test_ct01_controls_pass():
    report = _make_report(config_tag="ct01-ref", regime_tag="ct01-no-superluminal")
    rows = ct01_compare_surfaces(report, report, tolerances=ct01_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_ct01_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="ct01-neg-fp-ref", regime_tag="ct01-no-superluminal")
    cand = _make_report(config_tag="ct01-neg-fp-cand", regime_tag="ct01-no-superluminal")
    _write_ct01_report(tmp_path / "ct01_reference_report.json", ref)
    _write_ct01_report(tmp_path / "ct01_candidate_report.json", cand, tamper_fingerprint=True)

    rec = ct01_no_superluminal_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_ct01_blocks_when_artifacts_missing(tmp_path: Path):
    rec = ct01_no_superluminal_v0_record(
        date="2026-02-09",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
