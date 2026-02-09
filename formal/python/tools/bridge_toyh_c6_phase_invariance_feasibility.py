from __future__ import annotations

"""Feasibility gate for BRIDGE_TICKET_TOYH_0001 (C6 phase invariance).

Goal
- Verify a canonical, non-archive surface exists and exposes phase/gauge-like redundancy.
- Record deterministic feasibility diagnostics (no status upgrades).

Output schema (v1)
{
  "schema_version": 1,
  "bridge_id": "BRIDGE_TICKET_TOYH_0001",
  "canonical_surface": {...},
  "found": true|false,
  "checks": {...},
  "prerequisite": "..."
}
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
from pathlib import Path
from typing import Optional

import numpy as np

from formal.python.crft.cp_nlse_2d import (
    CPParams2D,
    Grid2D,
    compute_energy_2d,
    compute_norm_2d,
    rhs_cp_nlse_2d,
)

SURFACE_PATH = "formal/python/crft/cp_nlse_2d.py"


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def build_bridge_toyh_c6_phase_invariance_feasibility(*, repo_root: Path) -> dict:
    surface_file = repo_root / SURFACE_PATH
    if not surface_file.exists():
        return {
            "schema_version": 1,
            "bridge_id": "BRIDGE_TICKET_TOYH_0001",
            "canonical_surface": {"path": SURFACE_PATH, "sha256": None},
            "found": False,
            "checks": {},
            "prerequisite": "Canonical surface not found: formal/python/crft/cp_nlse_2d.py",
        }

    grid = Grid2D.from_box(Nx=16, Ny=16, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    theta = np.pi / 3.0
    phi0 = _plane_wave(grid, params.rho0)
    phi1 = phi0 * np.exp(1j * theta)

    n0 = compute_norm_2d(phi0, grid)
    n1 = compute_norm_2d(phi1, grid)
    e0 = compute_energy_2d(phi0, grid, params)
    e1 = compute_energy_2d(phi1, grid, params)

    rhs0 = rhs_cp_nlse_2d(phi0, grid, params)
    rhs1 = rhs_cp_nlse_2d(phi1, grid, params)
    rhs_equiv = rhs1 * np.exp(-1j * theta)

    norm_rel = abs(n1 - n0) / n0
    energy_rel = abs(e1 - e0) / max(1e-12, abs(e0))
    rhs_rel = float(np.linalg.norm(rhs_equiv - rhs0) / np.linalg.norm(rhs0))

    tol = 1e-10
    found = bool(norm_rel <= tol and energy_rel <= tol and rhs_rel <= tol)

    return {
        "schema_version": 1,
        "bridge_id": "BRIDGE_TICKET_TOYH_0001",
        "canonical_surface": {"path": SURFACE_PATH, "sha256": _sha256_path(surface_file)},
        "found": found,
        "checks": {
            "phase_theta": float(theta),
            "norm_rel_diff": float(norm_rel),
            "energy_rel_diff": float(energy_rel),
            "rhs_equiv_rel_err": float(rhs_rel),
            "tolerance": tol,
            "invariant_fields": ["norm_2d", "energy_2d", "rhs_equivariance"],
        },
        "prerequisite": "" if found else "C6 surface did not pass phase-invariance feasibility check.",
    }


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Feasibility gate for BRIDGE_TICKET_TOYH_0001.")
    parser.add_argument("--out", required=True, help="Repo-relative output JSON path")

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyh_c6_phase_invariance_feasibility(repo_root=repo_root)

    out_path = repo_root / args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(str(Path(args.out).as_posix()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
