from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl07_energy_noether_conservation_v0 import (
    RL07EnergyReport,
    RL07_TOLERANCE_PROFILE_ENV,
    rl07_compare_surfaces,
    rl07_energy_noether_conservation_v0_record,
    rl07_v0_tolerance_profile_from_env,
    rl07_v0_tolerances,
)
from formal.python.tools.rl07_energy_noether_conservation_front_door import generate_rl07_report


def _write_rl07_report(path: Path, report: RL07EnergyReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> RL07EnergyReport:
    return generate_rl07_report(
        nx=64,
        length=6.283185307179586,
        c=1.0,
        dt=0.1 * (6.283185307179586 / 64.0),
        steps=200,
        eps_drift=5e-3,
        eps_drop=0.10,
        gamma_negative=0.1,
        regime_tag=regime_tag,
        config_tag=config_tag,
        domain_tag="rl07-energy-noether-domain-01",
    )


def test_rl07_record_is_deterministic_and_schema_stable():
    rec1 = rl07_energy_noether_conservation_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl07_energy_noether_conservation_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-07_energy_noether_conservation_comparator/v0"
    assert rec1.observable_id == "OV-RL-07"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-07"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl07_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl07_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl07_v0_tolerance_profile_from_env({RL07_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="rl07-prof-ref", regime_tag="rl07-energy-noether")
    cand = _make_report(config_tag="rl07-prof-cand", regime_tag="rl07-energy-noether")
    _write_rl07_report(tmp_path / "rl07_reference_report.json", ref)
    _write_rl07_report(tmp_path / "rl07_candidate_report.json", cand)

    rec = rl07_energy_noether_conservation_v0_record(
        date="2026-02-09",
        env={RL07_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl07_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl07_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/energy_noether_front_door_report/v1"},
            {"schema": "RL/energy_noether_front_door_report/v1"},
            tolerances=rl07_v0_tolerances("pinned"),
        )


def test_rl07_negative_control_energy_drop_detected():
    report = _make_report(config_tag="rl07-neg-ref", regime_tag="rl07-energy-noether")
    rows = rl07_compare_surfaces(report, report, tolerances=rl07_v0_tolerances("pinned"))
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(neg_rows) == 1
    assert neg_rows[0]["passed"] is True


def test_rl07_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="rl07-neg-fp-ref", regime_tag="rl07-energy-noether")
    cand = _make_report(config_tag="rl07-neg-fp-cand", regime_tag="rl07-energy-noether")
    _write_rl07_report(tmp_path / "rl07_reference_report.json", ref)
    _write_rl07_report(tmp_path / "rl07_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl07_energy_noether_conservation_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl07_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl07_energy_noether_conservation_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
