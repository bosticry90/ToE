from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.ct09_independent_external_anchor_sound_speed_v0 import (
    CT09IndependentAnchorCase,
    CT09IndependentAnchorReport,
    CT09_TOLERANCE_PROFILE_ENV,
    ct09_compare_surfaces,
    ct09_independent_external_anchor_sound_speed_v0_record,
    ct09_v0_tolerance_profile_from_env,
    ct09_v0_tolerances,
)
from formal.python.tools.ct09_independent_external_anchor_sound_speed_front_door import build_ct09_reports


def _write_ct09_report(path: Path, report: CT09IndependentAnchorReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(
    *,
    config_tag: str,
    regime_tag: str,
    tolerance_profile: str = "pinned",
) -> CT09IndependentAnchorReport:
    report, _ = build_ct09_reports(tolerance_profile=tolerance_profile)
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return CT09IndependentAnchorReport(
        schema=payload["schema"],
        config_tag=payload["config_tag"],
        regime_tag=payload["regime_tag"],
        domain_tag=payload["domain_tag"],
        params={k: payload["params"][k] for k in payload["params"]},
        boundary=str(payload["boundary"]),
        cases=[
            CT09IndependentAnchorCase(
                case_id=str(case["case_id"]),
                kind=str(case["kind"]),
                model_tag=str(case["model_tag"]),
                c_um_per_ms=float(case["c_um_per_ms"]),
                intercept_um=float(case["intercept_um"]),
                rmse_um=float(case["rmse_um"]),
                max_abs_error_um=float(case["max_abs_error_um"]),
                reduced_chi2=float(case["reduced_chi2"]),
                n_points=int(case["n_points"]),
            )
            for case in payload["cases"]
        ],
    )


def test_ct09_record_is_deterministic_and_schema_stable():
    rec1 = ct09_independent_external_anchor_sound_speed_v0_record(date="2026-02-11", tolerance_profile="pinned")
    rec2 = ct09_independent_external_anchor_sound_speed_v0_record(date="2026-02-11", tolerance_profile="pinned")

    assert rec1.schema == "CT-09_independent_external_anchor_sound_speed_comparator/v0"
    assert rec1.observable_id == "CT-09"
    assert rec1.domain_id == "CT-DOMAIN-09"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_ct09_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert ct09_v0_tolerance_profile_from_env({}) == "pinned"
    assert ct09_v0_tolerance_profile_from_env({CT09_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(
        config_tag="ct09-prof-ref",
        regime_tag="ct09-external-anchor",
        tolerance_profile="portable",
    )
    cand = _make_report(
        config_tag="ct09-prof-cand",
        regime_tag="ct09-external-anchor",
        tolerance_profile="portable",
    )
    _write_ct09_report(tmp_path / "ct09_reference_report.json", ref)
    _write_ct09_report(tmp_path / "ct09_candidate_report.json", cand)

    rec = ct09_independent_external_anchor_sound_speed_v0_record(
        date="2026-02-11",
        env={CT09_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False
    assert rec.summary["counts"]["fail"] == 0


def test_ct09_profile_mismatch_between_artifact_and_comparator_is_detected(tmp_path: Path):
    # Pinned artifacts compared under portable profile should fail via domain inconsistency.
    ref = _make_report(
        config_tag="ct09-prof-mismatch-ref",
        regime_tag="ct09-external-anchor",
        tolerance_profile="pinned",
    )
    cand = _make_report(
        config_tag="ct09-prof-mismatch-cand",
        regime_tag="ct09-external-anchor",
        tolerance_profile="pinned",
    )
    _write_ct09_report(tmp_path / "ct09_reference_report.json", ref)
    _write_ct09_report(tmp_path / "ct09_candidate_report.json", cand)

    rec = ct09_independent_external_anchor_sound_speed_v0_record(
        date="2026-02-11",
        env={CT09_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False
    assert rec.summary["counts"]["fail"] == 2
    assert all("FAIL_DOMAIN_PARAMETER_INCONSISTENT" in row["reason_codes"] for row in rec.rows)


def test_ct09_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        ct09_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "CT-09/independent_external_anchor_sound_speed_front_door_report/v1"},
            {"schema": "CT-09/independent_external_anchor_sound_speed_front_door_report/v1"},
            tolerances=ct09_v0_tolerances("pinned"),
        )


def test_ct09_controls_pass():
    report = _make_report(config_tag="ct09-ref", regime_tag="ct09-external-anchor")
    rows = ct09_compare_surfaces(report, report, tolerances=ct09_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control_model_break"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_ct09_config_tag_difference_is_non_binding_metadata():
    ref = _make_report(config_tag="ct09-config-ref", regime_tag="ct09-external-anchor")
    cand = _make_report(config_tag="ct09-config-cand", regime_tag="ct09-external-anchor")

    rows = ct09_compare_surfaces(ref, cand, tolerances=ct09_v0_tolerances("pinned"))
    assert len(rows) == 2
    assert all(row["passed"] is True for row in rows)
    assert all(row["source"]["reference_config_tag"] != row["source"]["candidate_config_tag"] for row in rows)


def test_ct09_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="ct09-neg-fp-ref", regime_tag="ct09-external-anchor")
    cand = _make_report(config_tag="ct09-neg-fp-cand", regime_tag="ct09-external-anchor")
    _write_ct09_report(tmp_path / "ct09_reference_report.json", ref)
    _write_ct09_report(tmp_path / "ct09_candidate_report.json", cand, tamper_fingerprint=True)

    rec = ct09_independent_external_anchor_sound_speed_v0_record(date="2026-02-11", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_ct09_blocks_when_artifacts_missing(tmp_path: Path):
    rec = ct09_independent_external_anchor_sound_speed_v0_record(
        date="2026-02-11",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
