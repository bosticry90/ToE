from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl01_relativistic_dispersion_v0 import (
    RL01DispersionReport,
    RL01_TOLERANCE_PROFILE_ENV,
    rl01_compare_dispersion_surfaces,
    rl01_relativistic_dispersion_v0_record,
    rl01_v0_tolerance_profile_from_env,
    rl01_v0_tolerances,
)


def _write_rl01_report(path: Path, report: RL01DispersionReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, k: list[float], c: float, m: float, config_tag: str, regime_tag: str) -> RL01DispersionReport:
    omega2 = [(c * c) * (kk * kk) + (m * m) for kk in k]
    return RL01DispersionReport(
        schema="RL/dispersion_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"c": c, "m": m},
        k=list(k),
        omega2=omega2,
    )


def test_rl01_record_is_deterministic_and_schema_stable():
    rec1 = rl01_relativistic_dispersion_v0_record(date="2026-02-08", tolerance_profile="pinned")
    rec2 = rl01_relativistic_dispersion_v0_record(date="2026-02-08", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-01_relativistic_dispersion_comparator/v0"
    assert rec1.observable_id == "OV-RL-01"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-01"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl01_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl01_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl01_v0_tolerance_profile_from_env({RL01_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-prof-ref", regime_tag="rl01-lowk")
    cand = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-prof-cand", regime_tag="rl01-lowk")
    _write_rl01_report(tmp_path / "rl01_reference_report.json", ref)
    _write_rl01_report(tmp_path / "rl01_candidate_report.json", cand)

    rec = rl01_relativistic_dispersion_v0_record(
        date="2026-02-08",
        env={RL01_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl01_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl01_compare_dispersion_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/dispersion_front_door_report/v1"},
            {"schema": "RL/dispersion_front_door_report/v1"},
            tolerances=rl01_v0_tolerances("pinned"),
        )


def test_rl01_negative_control_k_permutation_fails_order_or_alignment():
    k_ref = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k_ref, c=1.0, m=1.0, config_tag="rl01-neg-ref", regime_tag="rl01-lowk")
    cand = _make_report(k=[0.0, 0.5, 0.25, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-neg-k", regime_tag="rl01-lowk")
    row = rl01_compare_dispersion_surfaces(ref, cand, tolerances=rl01_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert ("FAIL_K_GRID_ORDER" in reasons) or ("FAIL_K_GRID_ALIGNMENT" in reasons)


def test_rl01_negative_control_regime_mismatch_fails():
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k, c=1.0, m=1.0, config_tag="rl01-neg-regime-ref", regime_tag="rl01-lowk")
    cand = _make_report(k=k, c=1.0, m=1.0, config_tag="rl01-neg-regime-cand", regime_tag="rl01-highk")
    row = rl01_compare_dispersion_surfaces(ref, cand, tolerances=rl01_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_REGIME_MISMATCH" in reasons


def test_rl01_negative_control_shape_mismatch_fails():
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k, c=1.0, m=1.0, config_tag="rl01-neg-shape-ref", regime_tag="rl01-lowk")
    cand = RL01DispersionReport(
        schema="RL/dispersion_front_door_report/v1",
        config_tag="rl01-neg-shape-cand",
        regime_tag="rl01-lowk",
        params={"c": 1.0, "m": 1.0},
        k=list(k),
        omega2=[(1.0 * 1.0) * (kk * kk) + (1.0 * 1.0) + 0.5 * kk for kk in k],
    )
    row = rl01_compare_dispersion_surfaces(ref, cand, tolerances=rl01_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_REL_LIMIT_SHAPE_MISMATCH" in reasons


def test_rl01_fingerprint_tamper_negative_control_fails_nondeterministic(tmp_path: Path):
    ref = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-neg-fp-ref", regime_tag="rl01-lowk")
    cand = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-neg-fp-cand", regime_tag="rl01-lowk")
    _write_rl01_report(tmp_path / "rl01_reference_report.json", ref)
    _write_rl01_report(tmp_path / "rl01_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl01_relativistic_dispersion_v0_record(date="2026-02-08", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    row = rec.rows[0]
    assert row["passed"] is False
    assert "FAIL_REL_LIMIT_NONDETERMINISTIC" in list(row["reason_codes"])


def test_rl01_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl01_relativistic_dispersion_v0_record(date="2026-02-08", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
