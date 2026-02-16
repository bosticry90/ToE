from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl12_lorentz_poincare_invariance_proxy_v0 import (
    RL12LorentzReport,
    RL12_TOLERANCE_PROFILE_ENV,
    rl12_compare_surfaces,
    rl12_lorentz_poincare_invariance_proxy_v0_record,
    rl12_v0_tolerance_profile_from_env,
    rl12_v0_tolerances,
)
from formal.python.tools.rl12_lorentz_poincare_invariance_proxy_front_door import build_rl12_reports


def _write_rl12_report(path: Path, report: RL12LorentzReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> RL12LorentzReport:
    report, _ = build_rl12_reports()
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return RL12LorentzReport(
        schema=payload["schema"],
        config_tag=payload["config_tag"],
        regime_tag=payload["regime_tag"],
        domain_tag=payload["domain_tag"],
        params={k: float(v) for k, v in payload["params"].items()},
        boundary=str(payload["boundary"]),
        x=[float(v) for v in payload["x"]],
        t=[float(v) for v in payload["t"]],
        cases=[
            type(report.cases[0])(
                case_id=str(case["case_id"]),
                kind=str(case["kind"]),
                invariant_metric=float(case["invariant_metric"]),
                u=[float(v) for v in case["u"]],
                u_boosted=[float(v) for v in case["u_boosted"]],
            )
            for case in payload["cases"]
        ],
    )


def test_rl12_record_is_deterministic_and_schema_stable():
    rec1 = rl12_lorentz_poincare_invariance_proxy_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl12_lorentz_poincare_invariance_proxy_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-12_lorentz_poincare_invariance_proxy_comparator/v0"
    assert rec1.observable_id == "OV-RL-12"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-12"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl12_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl12_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl12_v0_tolerance_profile_from_env({RL12_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="rl12-prof-ref", regime_tag="rl12-lorentz-poincare")
    cand = _make_report(config_tag="rl12-prof-cand", regime_tag="rl12-lorentz-poincare")
    _write_rl12_report(tmp_path / "rl12_reference_report.json", ref)
    _write_rl12_report(tmp_path / "rl12_candidate_report.json", cand)

    rec = rl12_lorentz_poincare_invariance_proxy_v0_record(
        date="2026-02-09",
        env={RL12_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl12_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl12_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/lorentz_poincare_invariance_front_door_report/v1"},
            {"schema": "RL/lorentz_poincare_invariance_front_door_report/v1"},
            tolerances=rl12_v0_tolerances("pinned"),
        )


def test_rl12_controls_pass():
    report = _make_report(config_tag="rl12-ref", regime_tag="rl12-lorentz-poincare")
    rows = rl12_compare_surfaces(report, report, tolerances=rl12_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_rl12_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="rl12-neg-fp-ref", regime_tag="rl12-lorentz-poincare")
    cand = _make_report(config_tag="rl12-neg-fp-cand", regime_tag="rl12-lorentz-poincare")
    _write_rl12_report(tmp_path / "rl12_reference_report.json", ref)
    _write_rl12_report(tmp_path / "rl12_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl12_lorentz_poincare_invariance_proxy_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl12_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl12_lorentz_poincare_invariance_proxy_v0_record(
        date="2026-02-09",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
