from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

from formal.python.toe.comparators.rl03_weak_field_poisson_v0 import (
    RL03PoissonReport,
    RL03_TOLERANCE_PROFILE_ENV,
    rl03_compare_surfaces,
    rl03_v0_tolerance_profile_from_env,
    rl03_v0_tolerances,
    rl03_weak_field_poisson_v0_record,
)


def _write_rl03_report(path: Path, report: RL03PoissonReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(
    *,
    x: list[float],
    rho: list[float],
    phi: list[float],
    kappa: float,
    length: float,
    nx: int,
    config_tag: str,
    regime_tag: str,
) -> RL03PoissonReport:
    return RL03PoissonReport(
        schema="RL/weak_field_poisson_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"kappa": kappa, "length": length, "nx": float(nx)},
        boundary="periodic",
        gauge="mean_zero",
        x=list(x),
        rho=list(rho),
        phi=list(phi),
    )


def _make_grid(nx: int = 8, length: float = 6.283185307179586) -> np.ndarray:
    return np.linspace(0.0, float(length), int(nx), endpoint=False)


def test_rl03_record_is_deterministic_and_schema_stable():
    rec1 = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-03_weak_field_poisson_comparator/v0"
    assert rec1.observable_id == "OV-RL-03"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-03"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl03_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl03_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl03_v0_tolerance_profile_from_env({RL03_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    x = _make_grid()
    rho = np.exp(-0.5 * ((x - 3.141592653589793) / 0.5) ** 2)
    phi = np.zeros_like(x)
    ref = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-prof-ref",
        regime_tag="rl03-weak-field",
    )
    cand = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-prof-cand",
        regime_tag="rl03-weak-field",
    )
    _write_rl03_report(tmp_path / "rl03_reference_report.json", ref)
    _write_rl03_report(tmp_path / "rl03_candidate_report.json", cand)

    rec = rl03_weak_field_poisson_v0_record(
        date="2026-02-09",
        env={RL03_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl03_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl03_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/weak_field_poisson_front_door_report/v1"},
            {"schema": "RL/weak_field_poisson_front_door_report/v1"},
            tolerances=rl03_v0_tolerances("pinned"),
        )


def test_rl03_negative_control_x_permutation_fails_order_or_alignment():
    x_ref = _make_grid()
    rho = np.exp(-0.5 * ((x_ref - 3.141592653589793) / 0.5) ** 2)
    phi = np.zeros_like(x_ref)
    ref = _make_report(
        x=list(x_ref),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x_ref),
        config_tag="rl03-neg-ref",
        regime_tag="rl03-weak-field",
    )
    cand = _make_report(
        x=list([x_ref[0], x_ref[2], x_ref[1], *x_ref[3:]]),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x_ref),
        config_tag="rl03-neg-x",
        regime_tag="rl03-weak-field",
    )
    row = rl03_compare_surfaces(ref, cand, tolerances=rl03_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert ("FAIL_X_GRID_ORDER" in reasons) or ("FAIL_X_GRID_ALIGNMENT" in reasons)


def test_rl03_negative_control_param_mismatch_fails_domain_consistency():
    x = _make_grid()
    rho = np.exp(-0.5 * ((x - 3.141592653589793) / 0.5) ** 2)
    phi = np.zeros_like(x)
    ref = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-ref",
        regime_tag="rl03-weak-field",
    )
    cand = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=2.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-param",
        regime_tag="rl03-weak-field",
    )
    row = rl03_compare_surfaces(ref, cand, tolerances=rl03_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_DOMAIN_PARAMETER_INCONSISTENT" in reasons


def test_rl03_negative_control_gauge_constraint_fails():
    x = _make_grid()
    rho = np.exp(-0.5 * ((x - 3.141592653589793) / 0.5) ** 2)
    phi = np.ones_like(x) * 0.01
    ref = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-ref",
        regime_tag="rl03-weak-field",
    )
    cand = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-gauge",
        regime_tag="rl03-weak-field",
    )
    row = rl03_compare_surfaces(ref, cand, tolerances=rl03_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_GAUGE_CONSTRAINT" in reasons


def test_rl03_negative_control_residual_mismatch_fails_poisson_residual():
    x = _make_grid()
    rho = np.exp(-0.5 * ((x - 3.141592653589793) / 0.5) ** 2)
    phi = np.sin(x)
    ref = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-ref",
        regime_tag="rl03-weak-field",
    )
    cand = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi + 0.1 * np.cos(x)),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-residual",
        regime_tag="rl03-weak-field",
    )
    row = rl03_compare_surfaces(ref, cand, tolerances=rl03_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_POISSON_RESIDUAL" in reasons


def test_rl03_fingerprint_tamper_negative_control_fails_nondeterministic(tmp_path: Path):
    x = _make_grid()
    rho = np.exp(-0.5 * ((x - 3.141592653589793) / 0.5) ** 2)
    phi = np.zeros_like(x)
    ref = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-fp-ref",
        regime_tag="rl03-weak-field",
    )
    cand = _make_report(
        x=list(x),
        rho=list(rho),
        phi=list(phi),
        kappa=1.0,
        length=6.283185307179586,
        nx=len(x),
        config_tag="rl03-neg-fp-cand",
        regime_tag="rl03-weak-field",
    )
    _write_rl03_report(tmp_path / "rl03_reference_report.json", ref)
    _write_rl03_report(tmp_path / "rl03_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    row = rec.rows[0]
    assert row["passed"] is False
    assert "FAIL_NONDETERMINISTIC_FINGERPRINT" in list(row["reason_codes"])


def test_rl03_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
