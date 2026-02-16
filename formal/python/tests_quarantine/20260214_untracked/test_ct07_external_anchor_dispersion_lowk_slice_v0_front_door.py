from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.ct07_external_anchor_dispersion_lowk_slice_v0 import (
    CT07ExternalAnchorLowKCase,
    CT07ExternalAnchorLowKReport,
    CT07_TOLERANCE_PROFILE_ENV,
    ct07_compare_surfaces,
    ct07_external_anchor_dispersion_lowk_slice_v0_record,
    ct07_v0_tolerance_profile_from_env,
    ct07_v0_tolerances,
)
from formal.python.tools.ct07_external_anchor_dispersion_lowk_front_door import build_ct07_reports


def _write_ct07_report(path: Path, report: CT07ExternalAnchorLowKReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> CT07ExternalAnchorLowKReport:
    report, _ = build_ct07_reports()
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return CT07ExternalAnchorLowKReport(
        schema=payload["schema"],
        config_tag=payload["config_tag"],
        regime_tag=payload["regime_tag"],
        domain_tag=payload["domain_tag"],
        params={k: payload["params"][k] for k in payload["params"]},
        boundary=str(payload["boundary"]),
        cases=[
            CT07ExternalAnchorLowKCase(
                case_id=str(case["case_id"]),
                kind=str(case["kind"]),
                model_tag=str(case["model_tag"]),
                c_s2_kHz2_um2=float(case["c_s2_kHz2_um2"]),
                alpha_kHz2_um4=float(case["alpha_kHz2_um4"]),
                c_s2_scale=float(case["c_s2_scale"]),
                rmse_kHz=float(case["rmse_kHz"]),
                max_abs_error_kHz=float(case["max_abs_error_kHz"]),
                reduced_chi2=float(case["reduced_chi2"]),
                n_points=int(case["n_points"]),
            )
            for case in payload["cases"]
        ],
    )


def test_ct07_record_is_deterministic_and_schema_stable():
    rec1 = ct07_external_anchor_dispersion_lowk_slice_v0_record(date="2026-02-10", tolerance_profile="pinned")
    rec2 = ct07_external_anchor_dispersion_lowk_slice_v0_record(date="2026-02-10", tolerance_profile="pinned")

    assert rec1.schema == "CT-07_external_anchor_dispersion_lowk_slice_comparator/v0"
    assert rec1.observable_id == "CT-07"
    assert rec1.domain_id == "CT-DOMAIN-07"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_ct07_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert ct07_v0_tolerance_profile_from_env({}) == "pinned"
    assert ct07_v0_tolerance_profile_from_env({CT07_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="ct07-prof-ref", regime_tag="ct07-external-anchor-lowk")
    cand = _make_report(config_tag="ct07-prof-cand", regime_tag="ct07-external-anchor-lowk")
    _write_ct07_report(tmp_path / "ct07_reference_report.json", ref)
    _write_ct07_report(tmp_path / "ct07_candidate_report.json", cand)

    rec = ct07_external_anchor_dispersion_lowk_slice_v0_record(
        date="2026-02-10",
        env={CT07_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_ct07_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        ct07_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "CT-07/external_anchor_dispersion_lowk_front_door_report/v1"},
            {"schema": "CT-07/external_anchor_dispersion_lowk_front_door_report/v1"},
            tolerances=ct07_v0_tolerances("pinned"),
        )


def test_ct07_controls_pass():
    report = _make_report(config_tag="ct07-ref", regime_tag="ct07-external-anchor-lowk")
    rows = ct07_compare_surfaces(report, report, tolerances=ct07_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control_model_break"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_ct07_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="ct07-neg-fp-ref", regime_tag="ct07-external-anchor-lowk")
    cand = _make_report(config_tag="ct07-neg-fp-cand", regime_tag="ct07-external-anchor-lowk")
    _write_ct07_report(tmp_path / "ct07_reference_report.json", ref)
    _write_ct07_report(tmp_path / "ct07_candidate_report.json", cand, tamper_fingerprint=True)

    rec = ct07_external_anchor_dispersion_lowk_slice_v0_record(date="2026-02-10", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_ct07_blocks_when_artifacts_missing(tmp_path: Path):
    rec = ct07_external_anchor_dispersion_lowk_slice_v0_record(
        date="2026-02-10",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}

