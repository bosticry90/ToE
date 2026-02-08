from __future__ import annotations

import json
from pathlib import Path
import re

from formal.python.toe.comparators.cv01_bec_bragg_v1 import (
    CV01_TOLERANCE_PROFILE_ENV,
    cv01_bec_bragg_v1_record,
    cv01_v1_compare_curved_fit,
    cv01_v1_cross_artifact_speed_residual,
    cv01_v1_tolerance_profile_from_env,
    cv01_v1_tolerances,
    render_cv01_v1_lock_markdown,
)
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    assert m is not None
    return json.loads(m.group(1))


def test_cv01_v1_record_is_deterministic_and_schema_stable():
    rec1 = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")
    rec2 = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")

    assert rec1.schema == "OV-CV-01_bec_bragg_v1_comparator/v1"
    assert rec1.observable_id == "OV-CV-01"
    assert rec1.domain_id == "DRBR-DOMAIN-01"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_cv01_v1_default_profile_is_pinned():
    profile = cv01_v1_tolerance_profile_from_env({})
    assert profile == "pinned"


def test_cv01_v1_portable_profile_from_env():
    profile = cv01_v1_tolerance_profile_from_env({CV01_TOLERANCE_PROFILE_ENV: "portable"})
    assert profile == "portable"

    rec = cv01_bec_bragg_v1_record(
        date="2026-02-08",
        env={CV01_TOLERANCE_PROFILE_ENV: "portable"},
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_cv01_v1_cross_artifact_negative_control_has_reason_code():
    sample = ((1.0, 1.0), (2.0, 2.0), (3.0, 3.0))
    linear = DR01Fit1D(
        u=0.0,
        c_s=1.0,
        tag="cv01-v1-linear-neg",
        source_kind="synthetic",
        source_ref="pytest",
        fit_method_tag="negative-control",
        sample_kw=sample,
    )
    curved = DR01FitCurved1D(
        u=0.0,
        c0=1.5,
        beta=0.0,
        tag="cv01-v1-curved-neg",
        source_kind="synthetic",
        source_ref="pytest",
        fit_method_tag="negative-control",
        sample_kw=sample,
    )
    cross = cv01_v1_cross_artifact_speed_residual(
        linear,
        curved,
        tol_cross_artifact=0.1,
    )
    assert bool(cross["passed"]) is False
    assert "cv01_fail_linear_vs_curved_speed_inconsistent" in list(cross["reason_codes"])


def test_cv01_v1_curved_negative_control_nonpositive_c0_fails():
    sample = ((1.0, 1.0), (2.0, 2.0), (3.0, 3.0))
    bad_curved = DR01FitCurved1D(
        u=0.0,
        c0=-1.0,
        beta=0.0,
        tag="cv01-v1-curved-nonpositive",
        source_kind="synthetic",
        source_ref="pytest",
        fit_method_tag="negative-control",
        sample_kw=sample,
    )
    row = cv01_v1_compare_curved_fit(bad_curved, tolerances=cv01_v1_tolerances("pinned"))
    assert bool(row["passed"]) is False
    assert "cv01_fail_nonpositive_declared_c0" in list(row["reason_codes"])


def test_cv01_v1_rows_and_cross_artifact_surface_present():
    rec = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")
    assert rec.status["blocked"] is False
    assert len(rec.rows) == 2

    for row in rec.rows:
        assert isinstance(bool(row.get("passed")), bool)
        reasons = list(row.get("reason_codes") or [])
        assert len(reasons) >= 1

    cross = dict(rec.cross_artifact)
    assert cross["check_id"] == "linear_vs_curved_speed_residual"
    assert isinstance(bool(cross.get("passed")), bool)
    assert len(list(cross.get("reason_codes") or [])) >= 1


def test_cv01_v1_lock_render_contains_record_and_fingerprint():
    rec = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")
    md = render_cv01_v1_lock_markdown(rec)
    payload = _extract_json_block(md)
    assert payload == rec.to_jsonable()
    assert f"Record fingerprint: `{rec.fingerprint()}`" in md


def test_cv01_v1_blocks_when_domain_artifacts_missing(tmp_path: Path):
    rec = cv01_bec_bragg_v1_record(
        date="2026-02-08",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    cross = dict(rec.cross_artifact)
    assert cross["check_id"] == "linear_vs_curved_speed_residual"
    assert cross["reason_codes"] == ["cv01_fail_cross_artifact_missing_inputs"]
    assert set(cross.keys()) == {
        "check_id",
        "input_fingerprints",
        "input_data_fingerprints",
        "speed_linear",
        "speed_curved",
        "speed_residual",
        "tolerance",
        "passed",
        "reason_codes",
    }
