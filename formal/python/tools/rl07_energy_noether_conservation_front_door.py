from __future__ import annotations

"""RL07 energy/Noether conservation front door artifact writer (v0)."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.rl07_energy_noether_conservation_v0 import (
    RL07EnergyCase,
    RL07EnergyReport,
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
    return repo_root / "formal" / "external_evidence" / "rl07_energy_noether_conservation_domain_01"


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
    gamma: float,
) -> tuple[float, float, float, float, float]:
    u = u0.copy()
    v = v0.copy()
    e0 = _energy(u, v, c=c, dx=dx)
    max_rel_drift = 0.0

    for _ in range(int(steps)):
        accel = (c * c) * _dxx_periodic(u, dx=dx) - float(gamma) * v
        v_half = v + 0.5 * dt * accel
        u = u + dt * v_half
        accel_next = (c * c) * _dxx_periodic(u, dx=dx) - float(gamma) * v_half
        v = v_half + 0.5 * dt * accel_next

        e_now = _energy(u, v, c=c, dx=dx)
        rel_drift_now = abs(e_now - e0) / e0 if e0 > 0.0 else 0.0
        max_rel_drift = max(max_rel_drift, rel_drift_now)

    et = _energy(u, v, c=c, dx=dx)
    rel_drift = abs(et - e0) / e0 if e0 > 0.0 else 0.0
    rel_drop = (e0 - et) / e0 if e0 > 0.0 else 0.0
    return e0, et, rel_drift, rel_drop, max_rel_drift


def generate_rl07_report(
    *,
    nx: int,
    length: float,
    c: float,
    dt: float,
    steps: int,
    eps_drift: float,
    eps_drop: float,
    gamma_negative: float,
    regime_tag: str,
    config_tag: str,
    domain_tag: str,
) -> RL07EnergyReport:
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    u0 = np.sin(x)
    v0 = np.zeros_like(u0)
    dx = float(length) / float(nx)

    e0, et, rel_drift, rel_drop, max_rel_drift = _simulate_case(
        u0=u0,
        v0=v0,
        c=c,
        dt=dt,
        dx=dx,
        steps=steps,
        gamma=0.0,
    )
    positive = RL07EnergyCase(
        case_id="POSITIVE",
        kind="positive_control",
        gamma=0.0,
        e0=e0,
        et=et,
        rel_drift=rel_drift,
        rel_drop=rel_drop,
        max_rel_drift=max_rel_drift,
    )

    e0, et, rel_drift, rel_drop, max_rel_drift = _simulate_case(
        u0=u0,
        v0=v0,
        c=c,
        dt=dt,
        dx=dx,
        steps=steps,
        gamma=gamma_negative,
    )
    negative = RL07EnergyCase(
        case_id="NEGATIVE",
        kind="negative_control",
        gamma=float(gamma_negative),
        e0=e0,
        et=et,
        rel_drift=rel_drift,
        rel_drop=rel_drop,
        max_rel_drift=max_rel_drift,
    )

    return RL07EnergyReport(
        schema="RL/energy_noether_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        domain_tag=domain_tag,
        params={
            "length": float(length),
            "nx": float(nx),
            "dx": float(dx),
            "c": float(c),
            "dt": float(dt),
            "steps": float(steps),
            "eps_drift": float(eps_drift),
            "eps_drop": float(eps_drop),
        },
        boundary="periodic",
        x=[float(v) for v in x],
        cases=[positive, negative],
    )


def write_rl07_reports(
    *,
    out_dir: Path,
    nx: int,
    length: float,
    c: float,
    dt: float,
    steps: int,
    eps_drift: float,
    eps_drop: float,
    gamma_negative: float,
    regime_tag: str,
    domain_tag: str,
) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    ref = generate_rl07_report(
        nx=nx,
        length=length,
        c=c,
        dt=dt,
        steps=steps,
        eps_drift=eps_drift,
        eps_drop=eps_drop,
        gamma_negative=gamma_negative,
        regime_tag=regime_tag,
        config_tag="rl07-ref-pinned",
        domain_tag=domain_tag,
    )
    cand = generate_rl07_report(
        nx=nx,
        length=length,
        c=c,
        dt=dt,
        steps=steps,
        eps_drift=eps_drift,
        eps_drop=eps_drop,
        gamma_negative=gamma_negative,
        regime_tag=regime_tag,
        config_tag="rl07-cand-pinned",
        domain_tag=domain_tag,
    )

    ref_path = out_dir / "rl07_reference_report.json"
    cand_path = out_dir / "rl07_candidate_report.json"

    ref_path.write_text(json_dumps(ref.to_jsonable()) + "\n", encoding="utf-8")
    cand_path.write_text(json_dumps(cand.to_jsonable()) + "\n", encoding="utf-8")

    return ref_path, cand_path


def json_dumps(payload: object) -> str:
    import json

    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Write RL07 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL07 artifacts.")
    parser.add_argument("--nx", type=int, default=128, help="Pinned grid size.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi).")
    parser.add_argument("--c", type=float, default=1.0, help="Pinned wave speed.")
    parser.add_argument("--dt", type=float, default=None, help="Pinned time step (default 0.1*dx).")
    parser.add_argument("--steps", type=int, default=2000, help="Pinned step count.")
    parser.add_argument("--eps-drift", type=float, default=5e-3, help="Pinned drift tolerance.")
    parser.add_argument("--eps-drop", type=float, default=0.10, help="Pinned drop tolerance.")
    parser.add_argument("--gamma-negative", type=float, default=0.02, help="Pinned damping for negative control.")
    parser.add_argument("--regime-tag", type=str, default="rl07-energy-noether", help="Pinned regime tag.")
    parser.add_argument("--domain-tag", type=str, default="rl07-energy-noether-domain-01", help="Pinned domain tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)
    dx = float(args.length) / float(args.nx)
    dt = float(args.dt) if args.dt is not None else 0.1 * dx

    ref_path, cand_path = write_rl07_reports(
        out_dir=out_dir,
        nx=args.nx,
        length=args.length,
        c=args.c,
        dt=dt,
        steps=args.steps,
        eps_drift=args.eps_drift,
        eps_drop=args.eps_drop,
        gamma_negative=args.gamma_negative,
        regime_tag=args.regime_tag,
        domain_tag=args.domain_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
