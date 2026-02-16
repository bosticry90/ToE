from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.ct03_energy_causality_rep_variant_v0 import (
    CT03EnergyCausalityCase,
    CT03EnergyCausalityReport,
    ct03_v0_tolerances,
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "ct03_energy_causality_rep_variant_domain_01"


def _dxx_periodic(values: np.ndarray, *, dx: float) -> np.ndarray:
    return (np.roll(values, -1) - 2.0 * values + np.roll(values, 1)) / float(dx * dx)


def _dx_forward_periodic(values: np.ndarray, *, dx: float) -> np.ndarray:
    return (np.roll(values, -1) - values) / float(dx)


def _energy_forward(u: np.ndarray, v: np.ndarray, *, c: float, dx: float) -> float:
    du_dx = _dx_forward_periodic(u, dx=dx)
    return float(np.sum(0.5 * v * v + 0.5 * (c * c) * du_dx * du_dx) * dx)


def _simulate_case(
    *,
    u0: np.ndarray,
    v0: np.ndarray,
    c: float,
    dt: float,
    dx: float,
    steps: int,
    gamma: float,
) -> tuple[float, float, float, float, float]:
    u = u0.copy()
    v = v0.copy()
    e0 = _energy_forward(u, v, c=c, dx=dx)
    max_rel_drift = 0.0

    for _ in range(int(steps)):
        accel = (c * c) * _dxx_periodic(u, dx=dx) - float(gamma) * v
        v_half = v + 0.5 * dt * accel
        u = u + dt * v_half
        accel_next = (c * c) * _dxx_periodic(u, dx=dx) - float(gamma) * v_half
        v = v_half + 0.5 * dt * accel_next

        e_now = _energy_forward(u, v, c=c, dx=dx)
        rel_drift_now = abs(e_now - e0) / e0 if e0 > 0.0 else 0.0
        max_rel_drift = max(max_rel_drift, rel_drift_now)

    et = _energy_forward(u, v, c=c, dx=dx)
    rel_drift = abs(et - e0) / e0 if e0 > 0.0 else 0.0
    rel_drop = (e0 - et) / e0 if e0 > 0.0 else 0.0
    return e0, et, rel_drift, rel_drop, max_rel_drift


def build_ct03_reports(
    *,
    length: float = 6.283185307179586,
    nx: int = 144,
    c_wave: float = 1.0,
    dt_pos: float | None = None,
    dt_neg: float | None = None,
    steps_pos: int = 2000,
    steps_neg: int = 50,
    gamma_negative: float = 0.05,
    cfl_max: float = 1.0,
    tolerance_profile: str = "pinned",
) -> tuple[CT03EnergyCausalityReport, CT03EnergyCausalityReport]:
    tolerances = ct03_v0_tolerances(tolerance_profile)

    dx = float(length) / float(nx)
    dt_pos_val = float(dt_pos) if dt_pos is not None else 0.1 * dx
    dt_neg_val = float(dt_neg) if dt_neg is not None else 1.05 * dx

    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    u0 = np.sin(x)
    v0 = np.zeros_like(u0)

    e0, et, rel_drift, rel_drop, max_rel_drift = _simulate_case(
        u0=u0,
        v0=v0,
        c=c_wave,
        dt=dt_pos_val,
        dx=dx,
        steps=steps_pos,
        gamma=0.0,
    )
    cfl_pos = float(c_wave) * float(dt_pos_val) / float(dx)
    positive = CT03EnergyCausalityCase(
        case_id="POSITIVE",
        kind="positive_control",
        gamma=0.0,
        dt=float(dt_pos_val),
        steps=int(steps_pos),
        cfl=float(cfl_pos),
        rel_drift=float(rel_drift),
        rel_drop=float(rel_drop),
        max_rel_drift=float(max_rel_drift),
    )

    e0, et, rel_drift, rel_drop, max_rel_drift = _simulate_case(
        u0=u0,
        v0=v0,
        c=c_wave,
        dt=dt_neg_val,
        dx=dx,
        steps=steps_neg,
        gamma=gamma_negative,
    )
    cfl_neg = float(c_wave) * float(dt_neg_val) / float(dx)
    negative = CT03EnergyCausalityCase(
        case_id="NEGATIVE",
        kind="negative_control",
        gamma=float(gamma_negative),
        dt=float(dt_neg_val),
        steps=int(steps_neg),
        cfl=float(cfl_neg),
        rel_drift=float(rel_drift),
        rel_drop=float(rel_drop),
        max_rel_drift=float(max_rel_drift),
    )

    params = {
        "length": float(length),
        "nx": float(nx),
        "dx": float(dx),
        "c_wave": float(c_wave),
        "dt_pos": float(dt_pos_val),
        "dt_neg": float(dt_neg_val),
        "steps_pos": float(steps_pos),
        "steps_neg": float(steps_neg),
        "gamma_negative": float(gamma_negative),
        "cfl_max": float(cfl_max),
        "eps_drift": float(tolerances["eps_drift"]),
        "eps_drop": float(tolerances["eps_drop"]),
        "eps_break": float(tolerances["eps_break"]),
        "energy_representation": "forward_diff",
    }

    report = CT03EnergyCausalityReport(
        schema="CT-03/energy_causality_rep_variant_front_door_report/v1",
        config_tag="ct03_energy_causality_rep_variant_v0",
        regime_tag="CT03_Energy_Causality_Rep_Variant",
        domain_tag="ct03_energy_causality_rep_variant_domain_01",
        params=params,
        boundary="periodic",
        cases=[positive, negative],
    )

    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_ct03_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "ct03_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "ct03_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
