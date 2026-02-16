from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.ct01_no_superluminal_propagation_v0 import (
    CT01PropagationCase,
    CT01PropagationReport,
    ct01_v0_tolerances,
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
    return repo_root / "formal" / "external_evidence" / "ct01_no_superluminal_propagation_domain_01"


def _gaussian(x: float, *, x0: float, sigma: float, amplitude: float) -> float:
    return float(amplitude) * float(np.exp(-0.5 * ((x - float(x0)) / float(sigma)) ** 2))


def _first_crossing_time(
    *,
    t_grid: np.ndarray,
    x_target: float,
    x0: float,
    c_wave: float,
    sigma: float,
    amplitude: float,
    u_threshold: float,
) -> tuple[float, bool]:
    for t in t_grid:
        center = float(x0) + float(c_wave) * float(t)
        u_val = _gaussian(float(x_target), x0=center, sigma=sigma, amplitude=amplitude)
        if u_val >= float(u_threshold):
            return float(t), True
    return -1.0, False


def build_ct01_reports(
    *,
    length: float = 6.283185307179586,
    nx: int = 128,
    dt: float = 0.1,
    nt: int = 32,
    c_wave: float = 1.0,
    c_cone: float = 1.0,
    amplitude: float = 1.0,
    sigma: float = 0.2,
    x0: float | None = None,
    delta_x: float = 1.0,
    tolerance_profile: str = "pinned",
) -> tuple[CT01PropagationReport, CT01PropagationReport]:
    tolerances = ct01_v0_tolerances(tolerance_profile)
    u_threshold = float(tolerances["u_threshold"])
    x0_val = float(x0) if x0 is not None else 0.25 * float(length)
    support_radius = float(sigma) * float(np.sqrt(2.0 * np.log(float(amplitude) / float(u_threshold))))
    x_target = float(x0_val) + float(support_radius) + float(delta_x)

    t_grid = np.linspace(0.0, float(dt) * float(nt - 1), int(nt))

    t_cross_pos, crossed_pos = _first_crossing_time(
        t_grid=t_grid,
        x_target=x_target,
        x0=x0_val,
        c_wave=c_wave,
        sigma=sigma,
        amplitude=amplitude,
        u_threshold=u_threshold,
    )
    v_emp_pos = float(delta_x) / float(t_cross_pos) if t_cross_pos > 0.0 else 0.0

    t_cross_neg = float(dt)
    crossed_neg = True
    v_emp_neg = float(delta_x) / float(t_cross_neg)

    params = {
        "length": float(length),
        "nx": float(nx),
        "dt": float(dt),
        "nt": float(nt),
        "c_wave": float(c_wave),
        "c_cone": float(c_cone),
        "amplitude": float(amplitude),
        "sigma": float(sigma),
        "x0": float(x0_val),
        "delta_x": float(delta_x),
        "support_radius": float(support_radius),
        "u_threshold": float(u_threshold),
        "eps_ct01": float(tolerances["eps_ct01"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = CT01PropagationReport(
        schema="CT-01/no_superluminal_propagation_front_door_report/v1",
        config_tag="ct01_no_superluminal_propagation_v0",
        regime_tag="CT01_No_Superluminal_Propagation",
        domain_tag="ct01_no_superluminal_propagation_domain_01",
        params=params,
        boundary="periodic",
        cases=[
            CT01PropagationCase(
                case_id="positive_control",
                kind="positive_control",
                delta_x=float(delta_x),
                t_cross=float(t_cross_pos),
                v_emp=float(v_emp_pos),
                c_cone=float(c_cone),
                crossed=bool(crossed_pos),
                update_mode="baseline",
            ),
            CT01PropagationCase(
                case_id="negative_control",
                kind="negative_control",
                delta_x=float(delta_x),
                t_cross=float(t_cross_neg),
                v_emp=float(v_emp_neg),
                c_cone=float(c_cone),
                crossed=bool(crossed_neg),
                update_mode="teleport_step",
            ),
        ],
    )

    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_ct01_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "ct01_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "ct01_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
