from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

from formal.python.toe.comparators.rl04_continuity_v0 import (
    RL04ContinuityReport,
    RL04_TOLERANCE_PROFILE_ENV,
    rl04_compare_surfaces,
    rl04_v0_tolerance_profile_from_env,
    rl04_v0_tolerances,
    rl04_continuity_v0_record,
)


def _write_rl04_report(path: Path, report: RL04ContinuityReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(
    *,
    t: list[float],
    x: list[float],
    rho: list[list[float]],
    j: list[list[float]],
    length: float,
    dt: float,
    nx: int,
    nt: int,
    k: float,
    omega: float,
    amplitude: float,
    config_tag: str,
    regime_tag: str,
) -> RL04ContinuityReport:
    return RL04ContinuityReport(
        schema="RL/continuity_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={
            "length": length,
            "nx": float(nx),
            "dt": dt,
            "nt": float(nt),
            "k": k,
            "omega": omega,
            "amplitude": amplitude,
        },
        boundary="periodic",
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
    )


def _make_grid(nx: int = 8, nt: int = 4, length: float = 6.283185307179586, dt: float = 0.1) -> tuple[np.ndarray, np.ndarray]:
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    t = np.linspace(0.0, float(dt) * float(nt - 1), int(nt))
    return t, x


def test_rl04_record_is_deterministic_and_schema_stable():
    rec1 = rl04_continuity_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl04_continuity_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-04_continuity_comparator/v0"
    assert rec1.observable_id == "OV-RL-04"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-04"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl04_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl04_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl04_v0_tolerance_profile_from_env({RL04_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    t, x = _make_grid()
    phase = 1.0 * x[None, :] - 1.0 * t[:, None]
    rho = np.cos(phase)
    j = np.cos(phase)
    ref = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-prof-ref",
        regime_tag="rl04-continuity",
    )
    cand = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-prof-cand",
        regime_tag="rl04-continuity",
    )
    _write_rl04_report(tmp_path / "rl04_reference_report.json", ref)
    _write_rl04_report(tmp_path / "rl04_candidate_report.json", cand)

    rec = rl04_continuity_v0_record(
        date="2026-02-09",
        env={RL04_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl04_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl04_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/continuity_front_door_report/v1"},
            {"schema": "RL/continuity_front_door_report/v1"},
            tolerances=rl04_v0_tolerances("pinned"),
        )


def test_rl04_negative_control_x_permutation_fails_order_or_alignment():
    t, x_ref = _make_grid()
    phase = 1.0 * x_ref[None, :] - 1.0 * t[:, None]
    rho = np.cos(phase)
    j = np.cos(phase)
    ref = _make_report(
        t=list(t),
        x=list(x_ref),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x_ref),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-ref",
        regime_tag="rl04-continuity",
    )
    x_perm = list(x_ref)
    x_perm[1], x_perm[2] = x_perm[2], x_perm[1]
    cand = _make_report(
        t=list(t),
        x=x_perm,
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x_ref),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-x",
        regime_tag="rl04-continuity",
    )
    row = rl04_compare_surfaces(ref, cand, tolerances=rl04_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert ("FAIL_X_GRID_ORDER" in reasons) or ("FAIL_X_GRID_ALIGNMENT" in reasons)


def test_rl04_negative_control_param_mismatch_fails_domain_consistency():
    t, x = _make_grid()
    phase = 1.0 * x[None, :] - 1.0 * t[:, None]
    rho = np.cos(phase)
    j = np.cos(phase)
    ref = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-ref",
        regime_tag="rl04-continuity",
    )
    cand = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=2.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-param",
        regime_tag="rl04-continuity",
    )
    row = rl04_compare_surfaces(ref, cand, tolerances=rl04_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_DOMAIN_PARAMETER_INCONSISTENT" in reasons


def test_rl04_negative_control_continuity_residual_fails():
    t, x = _make_grid()
    phase = 1.0 * x[None, :] - 1.0 * t[:, None]
    rho = np.cos(phase)
    j = np.cos(phase) + 0.1 * np.sin(phase)
    ref = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-ref",
        regime_tag="rl04-continuity",
    )
    cand = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-residual",
        regime_tag="rl04-continuity",
    )
    row = rl04_compare_surfaces(ref, cand, tolerances=rl04_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_CONTINUITY_RESIDUAL" in reasons


def test_rl04_fingerprint_tamper_negative_control_fails_nondeterministic(tmp_path: Path):
    t, x = _make_grid()
    phase = 1.0 * x[None, :] - 1.0 * t[:, None]
    rho = np.cos(phase)
    j = np.cos(phase)
    ref = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-fp-ref",
        regime_tag="rl04-continuity",
    )
    cand = _make_report(
        t=list(t),
        x=list(x),
        rho=[list(row) for row in rho],
        j=[list(row) for row in j],
        length=6.283185307179586,
        dt=0.1,
        nx=len(x),
        nt=len(t),
        k=1.0,
        omega=1.0,
        amplitude=1.0,
        config_tag="rl04-neg-fp-cand",
        regime_tag="rl04-continuity",
    )
    _write_rl04_report(tmp_path / "rl04_reference_report.json", ref)
    _write_rl04_report(tmp_path / "rl04_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl04_continuity_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    row = rec.rows[0]
    assert row["passed"] is False
    assert "FAIL_NONDETERMINISTIC_FINGERPRINT" in list(row["reason_codes"])


def test_rl04_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl04_continuity_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
