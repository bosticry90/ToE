from __future__ import annotations

"""Bridge boundary report for BRIDGE_TICKET_TOYH_0002 (quarantine-safe).

Goal
- Produce a deterministic, bounded scan of current-magnitude invariance behavior
  for C6 under Toy-H global gauge transforms.
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

from formal.python.crft.cp_nlse_2d import CPParams2D, Grid2D, grad2_2d


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_bytes(data: bytes) -> str:
    h = hashlib.sha256()
    h.update(data)
    return h.hexdigest()


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def _current_l2(phi: np.ndarray, grid: Grid2D) -> float:
    phi_x, phi_y = grad2_2d(phi, grid)
    jx = np.imag(np.conjugate(phi) * phi_x)
    jy = np.imag(np.conjugate(phi) * phi_y)
    return float(np.sum((jx * jx + jy * jy).real) * grid.dx * grid.dy)


def _metrics(*, theta: float, Nx: int, alpha: float) -> dict:
    Ny = Nx
    grid = Grid2D.from_box(Nx=Nx, Ny=Ny, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = phi0 * np.exp(1j * theta)
    phi_shear = phi0 * np.exp(1j * alpha * grid.x)

    c0 = _current_l2(phi0, grid)
    c1 = _current_l2(phi1, grid)
    c_shear = _current_l2(phi_shear, grid)

    return {
        "current_l2_rel": float(abs(c1 - c0) / max(1e-12, abs(c0))),
        "local_phase_shear_rel": float(abs(c_shear - c0) / max(1e-12, abs(c0))),
    }


def build_bridge_toyh_c6_current_invariance_boundary_report(*, repo_root: Path) -> dict:
    _ = repo_root

    thetas = [0.0, float(np.pi / 6.0), float(np.pi / 3.0), float(np.pi / 2.0)]
    grid_sizes = [7, 9, 11]
    alpha = 0.5

    tol = 1e-10
    control_min = 1e-3

    samples: list[dict] = []
    for theta in thetas:
        for n in grid_sizes:
            metrics = _metrics(theta=theta, Nx=n, alpha=alpha)
            invariance_ok = metrics["current_l2_rel"] <= tol
            local_control_ok = metrics["local_phase_shear_rel"] > control_min

            if not invariance_ok:
                reason = "FAIL_CURRENT_INVARIANCE_TOL"
            elif not local_control_ok:
                reason = "FAIL_LOCAL_PHASE_SHEAR_CONTROL_NOT_TRIGGERED"
            else:
                reason = "PASS_CURRENT_INVARIANCE"

            samples.append(
                {
                    "theta": _q(theta),
                    "grid_n": int(n),
                    "current_l2_rel": _q(metrics["current_l2_rel"]),
                    "local_phase_shear_rel": _q(metrics["local_phase_shear_rel"]),
                    "invariance_ok": bool(invariance_ok),
                    "local_control_ok": bool(local_control_ok),
                    "reason_code": reason,
                }
            )

    passed = [s for s in samples if s["reason_code"] == "PASS_CURRENT_INVARIANCE"]
    failed = [s for s in samples if s["reason_code"] != "PASS_CURRENT_INVARIANCE"]

    item = {
        "ticket_id": "BRIDGE_TICKET_TOYH_0002",
        "scan_id": "c6_current_invariance_boundary_scan_v1",
        "inputs": {
            "thetas": [_q(t) for t in thetas],
            "grid_sizes": list(grid_sizes),
            "local_phase_shear_alpha": float(alpha),
            "tolerance": tol,
            "control_min": control_min,
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_invariant_observables",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_negative_control_local_phase_shear",
                "formal/python/tests/test_bridge_toyh_c6_current_invariance.py::test_bridge_toyh_c6_current_invariance_resolution_scan",
            ]
        },
        "samples": samples,
        "summary": {
            "n_samples": len(samples),
            "n_pass": len(passed),
            "n_fail": len(failed),
            "fail_reason_counts": {
                "FAIL_CURRENT_INVARIANCE_TOL": sum(
                    1 for s in failed if s["reason_code"] == "FAIL_CURRENT_INVARIANCE_TOL"
                ),
                "FAIL_LOCAL_PHASE_SHEAR_CONTROL_NOT_TRIGGERED": sum(
                    1 for s in failed if s["reason_code"] == "FAIL_LOCAL_PHASE_SHEAR_CONTROL_NOT_TRIGGERED"
                ),
            },
        },
    }

    payload = {
        "schema_version": 1,
        "items": [item],
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the deterministic Toy-H C6 current invariance boundary report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_invariance_BOUNDARY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_invariance_BOUNDARY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyh_c6_current_invariance_boundary_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
