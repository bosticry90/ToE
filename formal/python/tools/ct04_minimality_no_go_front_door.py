from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.ct04_minimality_no_go_v0 import (
    CT04MinimalityCase,
    CT04MinimalityReport,
    ct04_v0_tolerances,
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
    return repo_root / "formal" / "external_evidence" / "ct04_minimality_no_go_domain_01"


def _dxx_periodic(values: np.ndarray, *, dx: float) -> np.ndarray:
    return (np.roll(values, -1) - 2.0 * values + np.roll(values, 1)) / float(dx * dx)


def _dx_periodic(values: np.ndarray, *, dx: float) -> np.ndarray:
    return (np.roll(values, -1) - np.roll(values, 1)) / float(2.0 * dx)


def _energy(u: np.ndarray, v: np.ndarray, *, c: float, dx: float) -> float:
    du_dx = _dx_periodic(u, dx=dx)
    return float(np.sum(0.5 * v * v + 0.5 * (c * c) * du_dx * du_dx) * dx)


def _simulate_case(
    *,
    u0: np.ndarray,
    v0: np.ndarray,
    c: float,
    dt: float,
    dx: float,
    steps: int,
) -> tuple[float, float, float, float]:
    u = u0.copy()
    v = v0.copy()
    e0 = _energy(u, v, c=c, dx=dx)
    max_rel_drift = 0.0

    for _ in range(int(steps)):
        accel = (c * c) * _dxx_periodic(u, dx=dx)
        v_half = v + 0.5 * dt * accel
        u = u + dt * v_half
        accel_next = (c * c) * _dxx_periodic(u, dx=dx)
        v = v_half + 0.5 * dt * accel_next

        e_now = _energy(u, v, c=c, dx=dx)
        rel_drift_now = abs(e_now - e0) / e0 if e0 > 0.0 else 0.0
        max_rel_drift = max(max_rel_drift, rel_drift_now)

    et = _energy(u, v, c=c, dx=dx)
    rel_drift = abs(et - e0) / e0 if e0 > 0.0 else 0.0
    return e0, et, rel_drift, max_rel_drift


def build_ct04_reports(
    *,
    length: float = 6.283185307179586,
    nx: int = 128,
    c_wave: float = 1.0,
    dt_pos: float | None = None,
    dt_neg: float | None = None,
    steps_pos: int = 2000,
    steps_neg: int = 20,
    cfl_max: float = 1.0,
    tolerance_profile: str = "pinned",
) -> tuple[CT04MinimalityReport, CT04MinimalityReport]:
    tolerances = ct04_v0_tolerances(tolerance_profile)

    dx = float(length) / float(nx)
    dt_pos_val = float(dt_pos) if dt_pos is not None else 0.1 * dx
    dt_neg_val = float(dt_neg) if dt_neg is not None else 1.05 * dx

    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    u0 = np.sin(x)
    v0 = np.zeros_like(u0)

    e0, et, rel_drift, max_rel_drift = _simulate_case(
        u0=u0,
        v0=v0,
        c=c_wave,
        dt=dt_pos_val,
        dx=dx,
        steps=steps_pos,
    )
    cfl_pos = float(c_wave) * float(dt_pos_val) / float(dx)
    positive = CT04MinimalityCase(
        case_id="POSITIVE",
        kind="positive_control",
        constraint_mode="cfl_bound",
        dt=float(dt_pos_val),
        steps=int(steps_pos),
        cfl=float(cfl_pos),
        rel_drift=float(rel_drift),
        max_rel_drift=float(max_rel_drift),
    )

    e0, et, rel_drift, max_rel_drift = _simulate_case(
        u0=u0,
        v0=v0,
        c=c_wave,
        dt=dt_neg_val,
        dx=dx,
        steps=steps_neg,
    )
    cfl_neg = float(c_wave) * float(dt_neg_val) / float(dx)
    negative = CT04MinimalityCase(
        case_id="NEGATIVE",
        kind="negative_control",
        constraint_mode="cfl_removed",
        dt=float(dt_neg_val),
        steps=int(steps_neg),
        cfl=float(cfl_neg),
        rel_drift=float(rel_drift),
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
        "cfl_max": float(cfl_max),
        "eps_drift": float(tolerances["eps_drift"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = CT04MinimalityReport(
        schema="CT-04/minimality_no_go_front_door_report/v1",
        config_tag="ct04_minimality_no_go_v0",
        regime_tag="CT04_Minimality_No_Go",
        domain_tag="ct04_minimality_no_go_domain_01",
        params=params,
        boundary="periodic",
        cases=[positive, negative],
    )

    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_ct04_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "ct04_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "ct04_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
