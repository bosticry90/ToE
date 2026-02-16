from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

from formal.python.toe.comparators.rl06_phase_winding_quantization_v0 import (
    RL06PhaseWindingReport,
    RL06WindingCase,
    RL06_TOLERANCE_PROFILE_ENV,
    rl06_compare_surfaces,
    rl06_v0_tolerance_profile_from_env,
    rl06_v0_tolerances,
    rl06_phase_winding_quantization_v0_record,
)


def _write_rl06_report(path: Path, report: RL06PhaseWindingReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_case(*, x: np.ndarray, length: float, k: float, amplitude: float, case_id: str, kind: str) -> RL06WindingCase:
    theta = 2.0 * np.pi * float(k) * x / float(length)
    psi = float(amplitude) * np.exp(1j * theta)
    return RL06WindingCase(
        case_id=case_id,
        kind=kind,
        k_target=int(round(float(k))),
        psi_real=[float(v) for v in psi.real],
        psi_imag=[float(v) for v in psi.imag],
    )


def _make_report(*, x: np.ndarray, length: float, k_target: int, alpha_nonint: float, amplitude: float, config_tag: str, regime_tag: str) -> RL06PhaseWindingReport:
    quantized = _make_case(
        x=x,
        length=length,
        k=float(k_target),
        amplitude=amplitude,
        case_id="QUANTIZED",
        kind="quantized",
    )
    nonint_case = _make_case(
        x=x,
        length=length,
        k=float(k_target) + float(alpha_nonint),
        amplitude=amplitude,
        case_id="NONINT",
        kind="negative_control",
    )
    return RL06PhaseWindingReport(
        schema="RL/phase_winding_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={
            "length": float(length),
            "nx": float(len(x)),
            "k_target": float(k_target),
            "alpha_nonint": float(alpha_nonint),
            "amplitude": float(amplitude),
        },
        boundary="periodic",
        unwrap_method="cumulative_principal_value",
        x=[float(v) for v in x],
        cases=[quantized, nonint_case],
    )


def test_rl06_record_is_deterministic_and_schema_stable():
    rec1 = rl06_phase_winding_quantization_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl06_phase_winding_quantization_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-06_phase_winding_quantization_comparator/v0"
    assert rec1.observable_id == "OV-RL-06"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-06"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl06_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl06_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl06_v0_tolerance_profile_from_env({RL06_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    x = np.linspace(0.0, 6.283185307179586, 8, endpoint=False)
    ref = _make_report(
        x=x,
        length=6.283185307179586,
        k_target=2,
        alpha_nonint=0.35,
        amplitude=1.0,
        config_tag="rl06-prof-ref",
        regime_tag="rl06-phase-winding",
    )
    cand = _make_report(
        x=x,
        length=6.283185307179586,
        k_target=2,
        alpha_nonint=0.35,
        amplitude=1.0,
        config_tag="rl06-prof-cand",
        regime_tag="rl06-phase-winding",
    )
    _write_rl06_report(tmp_path / "rl06_reference_report.json", ref)
    _write_rl06_report(tmp_path / "rl06_candidate_report.json", cand)

    rec = rl06_phase_winding_quantization_v0_record(
        date="2026-02-09",
        env={RL06_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl06_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl06_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/phase_winding_front_door_report/v1"},
            {"schema": "RL/phase_winding_front_door_report/v1"},
            tolerances=rl06_v0_tolerances("pinned"),
        )


def test_rl06_negative_control_noninteger_detected():
    x = np.linspace(0.0, 6.283185307179586, 32, endpoint=False)
    report = _make_report(
        x=x,
        length=6.283185307179586,
        k_target=2,
        alpha_nonint=0.35,
        amplitude=1.0,
        config_tag="rl06-neg-ref",
        regime_tag="rl06-phase-winding",
    )
    rows = rl06_compare_surfaces(report, report, tolerances=rl06_v0_tolerances("pinned"))
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(neg_rows) == 1
    assert neg_rows[0]["passed"] is True


def test_rl06_fingerprint_tamper_negative_control_fails_nondeterministic(tmp_path: Path):
    x = np.linspace(0.0, 6.283185307179586, 8, endpoint=False)
    ref = _make_report(
        x=x,
        length=6.283185307179586,
        k_target=2,
        alpha_nonint=0.35,
        amplitude=1.0,
        config_tag="rl06-neg-fp-ref",
        regime_tag="rl06-phase-winding",
    )
    cand = _make_report(
        x=x,
        length=6.283185307179586,
        k_target=2,
        alpha_nonint=0.35,
        amplitude=1.0,
        config_tag="rl06-neg-fp-cand",
        regime_tag="rl06-phase-winding",
    )
    _write_rl06_report(tmp_path / "rl06_reference_report.json", ref)
    _write_rl06_report(tmp_path / "rl06_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl06_phase_winding_quantization_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl06_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl06_phase_winding_quantization_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
