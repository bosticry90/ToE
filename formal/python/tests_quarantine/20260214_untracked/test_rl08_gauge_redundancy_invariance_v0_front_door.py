from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl08_gauge_redundancy_invariance_v0 import (
    RL08GaugeReport,
    RL08_TOLERANCE_PROFILE_ENV,
    rl08_compare_surfaces,
    rl08_gauge_redundancy_invariance_v0_record,
    rl08_v0_tolerance_profile_from_env,
    rl08_v0_tolerances,
)
from formal.python.tools.rl08_gauge_redundancy_invariance_front_door import generate_rl08_report


def _write_rl08_report(path: Path, report: RL08GaugeReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> RL08GaugeReport:
    return generate_rl08_report(
        nx=64,
        length=6.283185307179586,
        alpha=0.2,
        eps_invariant=1e-10,
        eps_break=1e-3,
        regime_tag=regime_tag,
        config_tag=config_tag,
        domain_tag="rl08-gauge-redundancy-domain-01",
    )


def test_rl08_record_is_deterministic_and_schema_stable():
    rec1 = rl08_gauge_redundancy_invariance_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl08_gauge_redundancy_invariance_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-08_gauge_redundancy_invariance_comparator/v0"
    assert rec1.observable_id == "OV-RL-08"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-08"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl08_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl08_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl08_v0_tolerance_profile_from_env({RL08_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="rl08-prof-ref", regime_tag="rl08-gauge-redundancy")
    cand = _make_report(config_tag="rl08-prof-cand", regime_tag="rl08-gauge-redundancy")
    _write_rl08_report(tmp_path / "rl08_reference_report.json", ref)
    _write_rl08_report(tmp_path / "rl08_candidate_report.json", cand)

    rec = rl08_gauge_redundancy_invariance_v0_record(
        date="2026-02-09",
        env={RL08_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl08_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl08_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/gauge_redundancy_front_door_report/v1"},
            {"schema": "RL/gauge_redundancy_front_door_report/v1"},
            tolerances=rl08_v0_tolerances("pinned"),
        )


def test_rl08_negative_control_break_detected():
    report = _make_report(config_tag="rl08-neg-ref", regime_tag="rl08-gauge-redundancy")
    rows = rl08_compare_surfaces(report, report, tolerances=rl08_v0_tolerances("pinned"))
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(neg_rows) == 1
    assert neg_rows[0]["passed"] is True


def test_rl08_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="rl08-neg-fp-ref", regime_tag="rl08-gauge-redundancy")
    cand = _make_report(config_tag="rl08-neg-fp-cand", regime_tag="rl08-gauge-redundancy")
    _write_rl08_report(tmp_path / "rl08_reference_report.json", ref)
    _write_rl08_report(tmp_path / "rl08_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl08_gauge_redundancy_invariance_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl08_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl08_gauge_redundancy_invariance_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
