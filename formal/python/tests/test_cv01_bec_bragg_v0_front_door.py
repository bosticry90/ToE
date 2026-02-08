from __future__ import annotations

import json
from pathlib import Path
import re

from formal.python.toe.comparators.cv01_bec_bragg_v0 import (
    cv01_bec_bragg_v0_record,
    cv01_compare_curved_fit,
    cv01_compare_linear_fit,
    render_cv01_lock_markdown,
)
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D


REPO_ROOT = Path(__file__).resolve().parents[3]


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    assert m is not None
    return json.loads(m.group(1))


def test_cv01_record_is_deterministic_and_schema_stable():
    rec1 = cv01_bec_bragg_v0_record(date="2026-02-08")
    rec2 = cv01_bec_bragg_v0_record(date="2026-02-08")

    assert rec1.schema == "OV-CV-01_bec_bragg_v0_comparator/v1"
    assert rec1.observable_id == "OV-CV-01"
    assert rec1.domain_id == "DRBR-DOMAIN-01"
    assert rec1.comparator_role == "integrity_only"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_cv01_rows_have_pass_fail_and_reason_codes():
    rec = cv01_bec_bragg_v0_record(date="2026-02-08")
    assert rec.status["blocked"] is False
    assert len(rec.rows) == 2

    for row in rec.rows:
        assert isinstance(bool(row.get("passed")), bool)
        reasons = list(row.get("reason_codes") or [])
        assert len(reasons) >= 1

    counts = dict(rec.summary["counts"])
    assert int(counts["pass"]) + int(counts["fail"]) == len(rec.rows)
    assert int(counts["pass"]) >= 1
    assert "integrity_only" in list(rec.scope_limits)


def test_cv01_front_door_requires_typed_fit_objects():
    try:
        cv01_compare_linear_fit({"u": 0.0, "c_s": 1.0})  # type: ignore[arg-type]
        raised_linear = False
    except TypeError:
        raised_linear = True
    assert raised_linear

    try:
        cv01_compare_curved_fit({"u": 0.0, "c0": 1.0, "beta": 0.0})  # type: ignore[arg-type]
        raised_curved = False
    except TypeError:
        raised_curved = True
    assert raised_curved


def test_cv01_negative_control_nonpositive_declared_cs_fails_with_reason_code():
    neg = DR01Fit1D(
        u=0.0,
        c_s=-1.0,
        tag="cv01-neg-control",
        source_kind="synthetic",
        source_ref="pytest",
        fit_method_tag="negative-control",
        sample_kw=((1.0, -1.0), (2.0, -2.0), (3.0, -3.0)),
    )
    row = cv01_compare_linear_fit(neg)
    assert bool(row["passed"]) is False
    reasons = list(row["reason_codes"])
    assert "cv01_fail_nonpositive_declared_cs" in reasons


def test_cv01_lock_render_contains_record_and_fingerprint():
    rec = cv01_bec_bragg_v0_record(date="2026-02-08")
    md = render_cv01_lock_markdown(rec)

    payload = _extract_json_block(md)
    assert payload == rec.to_jsonable()
    assert f"Record fingerprint: `{rec.fingerprint()}`" in md


def test_cv01_blocks_when_domain_artifacts_missing(tmp_path: Path):
    rec = cv01_bec_bragg_v0_record(date="2026-02-08", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
