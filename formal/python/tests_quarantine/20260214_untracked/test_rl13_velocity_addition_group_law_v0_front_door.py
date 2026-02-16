from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl13_velocity_addition_group_law_v0 import (
    RL13VelocityReport,
    RL13_TOLERANCE_PROFILE_ENV,
    rl13_compare_surfaces,
    rl13_velocity_addition_group_law_v0_record,
    rl13_v0_tolerance_profile_from_env,
    rl13_v0_tolerances,
)
from formal.python.tools.rl13_velocity_addition_group_law_front_door import build_rl13_reports


def _write_rl13_report(path: Path, report: RL13VelocityReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> RL13VelocityReport:
    report, _ = build_rl13_reports()
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return RL13VelocityReport(
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
                beta_u=float(case["beta_u"]),
                beta_v=float(case["beta_v"]),
                beta_comp=float(case["beta_comp"]),
                beta_expected=float(case["beta_expected"]),
                addition_residual=float(case["addition_residual"]),
            )
            for case in payload["cases"]
        ],
    )


def test_rl13_record_is_deterministic_and_schema_stable():
    rec1 = rl13_velocity_addition_group_law_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl13_velocity_addition_group_law_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-13_velocity_addition_group_law_comparator/v0"
    assert rec1.observable_id == "OV-RL-13"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-13"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl13_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl13_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl13_v0_tolerance_profile_from_env({RL13_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="rl13-prof-ref", regime_tag="rl13-velocity-addition")
    cand = _make_report(config_tag="rl13-prof-cand", regime_tag="rl13-velocity-addition")
    _write_rl13_report(tmp_path / "rl13_reference_report.json", ref)
    _write_rl13_report(tmp_path / "rl13_candidate_report.json", cand)

    rec = rl13_velocity_addition_group_law_v0_record(
        date="2026-02-09",
        env={RL13_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl13_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl13_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/velocity_addition_front_door_report/v1"},
            {"schema": "RL/velocity_addition_front_door_report/v1"},
            tolerances=rl13_v0_tolerances("pinned"),
        )


def test_rl13_controls_pass():
    report = _make_report(config_tag="rl13-ref", regime_tag="rl13-velocity-addition")
    rows = rl13_compare_surfaces(report, report, tolerances=rl13_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_rl13_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="rl13-neg-fp-ref", regime_tag="rl13-velocity-addition")
    cand = _make_report(config_tag="rl13-neg-fp-cand", regime_tag="rl13-velocity-addition")
    _write_rl13_report(tmp_path / "rl13_reference_report.json", ref)
    _write_rl13_report(tmp_path / "rl13_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl13_velocity_addition_group_law_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl13_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl13_velocity_addition_group_law_v0_record(
        date="2026-02-09",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
