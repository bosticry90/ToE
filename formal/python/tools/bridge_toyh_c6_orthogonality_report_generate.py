from __future__ import annotations

"""Orthogonality audit for Toy-H ↔ C6 multi-constraint bridge family.

Goal
- Provide a deterministic, bounded audit that evaluates whether the two
  Toy-H ↔ C6 constraint channels (phase invariance, current invariance) are
  non-redundant on a shared pinned probe set.

Report schema (v1)
{
  "schema_version": 1,
  "report_id": "BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT",
  "shared_probe_set": {...},
  "items": [...],
  "summary": {...},
  "artifact_sha256": "..."
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

from formal.python.crft.cp_nlse_2d import CPParams2D, Grid2D, compute_energy_2d, compute_norm_2d, grad2_2d, rhs_cp_nlse_2d


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


def _angle_to_phasor(phi: float) -> complex:
    return complex(np.cos(float(phi)), np.sin(float(phi)))


def _phasor_dist(u1: complex, u2: complex) -> float:
    return float(abs(complex(u1) - complex(u2)))


def _stable_equivariance_phase_residual(*, base: np.ndarray, transformed: np.ndarray, theta: float) -> float:
    denom = max(float(np.vdot(base, base).real), 1e-12)
    alpha = complex(np.vdot(base, transformed) / denom)
    alpha_mag = max(abs(alpha), 1e-12)
    alpha_unit = alpha / alpha_mag
    target_unit = _angle_to_phasor(theta)
    return _phasor_dist(alpha_unit, target_unit)


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def _current_l2(phi: np.ndarray, grid: Grid2D) -> float:
    phi_x, phi_y = grad2_2d(phi, grid)
    jx = np.imag(np.conjugate(phi) * phi_x)
    jy = np.imag(np.conjugate(phi) * phi_y)
    return float(np.sum((jx * jx + jy * jy).real) * grid.dx * grid.dy)


def _phase_channel(
    *,
    theta: float,
    Nx: int,
    amplitude_scale: float,
    phase_sensitive_min: float,
    tol: float,
    use_stable_invariance: bool = False,
) -> dict:
    grid = Grid2D.from_box(Nx=Nx, Ny=Nx, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = amplitude_scale * phi0 * np.exp(1j * theta)

    n0 = compute_norm_2d(phi0, grid)
    n1 = compute_norm_2d(phi1, grid)
    e0 = compute_energy_2d(phi0, grid, params)
    e1 = compute_energy_2d(phi1, grid, params)

    rhs0 = rhs_cp_nlse_2d(phi0, grid, params)
    rhs1 = rhs_cp_nlse_2d(phi1, grid, params)
    rhs_equiv = rhs1 * np.exp(-1j * theta)
    rhs_rel_legacy = float(np.linalg.norm(rhs_equiv - rhs0) / max(1e-12, np.linalg.norm(rhs0)))
    rhs_phase_residual = _stable_equivariance_phase_residual(base=rhs0, transformed=rhs1, theta=theta)
    phase_field_residual = _stable_equivariance_phase_residual(base=phi0, transformed=phi1, theta=theta)

    norm_rel = float(abs(n1 - n0) / max(1e-12, abs(n0)))
    energy_rel = float(abs(e1 - e0) / max(1e-12, abs(e0)))
    rhs_rel = rhs_phase_residual if bool(use_stable_invariance) else rhs_rel_legacy
    phase_sensitive_delta = float(abs(phi1.real[0, 0] - phi0.real[0, 0]))

    invariance_residual = max(norm_rel, energy_rel, rhs_rel)
    if bool(use_stable_invariance):
        invariance_residual = max(norm_rel, energy_rel, phase_field_residual, rhs_phase_residual)
    invariance_ok = bool(invariance_residual <= tol)
    if theta == 0.0:
        control_ok = True
    else:
        control_ok = bool(phase_sensitive_delta > phase_sensitive_min)

    if not invariance_ok:
        reason = "FAIL_PHASE_INVARIANCE_TOL"
    elif not control_ok:
        reason = "FAIL_PHASE_CHANNEL_CONTROL_MIN"
    else:
        reason = "PASS"

    return {
        "pass": bool(reason == "PASS"),
        "reason_code": reason,
        "metrics": {
            "norm_rel": _q(norm_rel),
            "energy_rel": _q(energy_rel),
            "rhs_rel": _q(rhs_rel),
            "rhs_rel_legacy": _q(rhs_rel_legacy),
            "rhs_phase_residual": _q(rhs_phase_residual),
            "phase_field_residual": _q(phase_field_residual),
            "invariance_residual": _q(invariance_residual),
            "phase_sensitive_delta": _q(phase_sensitive_delta),
        },
    }


def _current_channel(
    *,
    theta: float,
    Nx: int,
    amplitude_scale: float,
    local_phase_shear_alpha: float,
    control_min: float,
    tol: float,
) -> dict:
    grid = Grid2D.from_box(Nx=Nx, Ny=Nx, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = amplitude_scale * phi0 * np.exp(1j * theta)
    phi_shear = phi0 * np.exp(1j * local_phase_shear_alpha * grid.x)

    c0 = _current_l2(phi0, grid)
    c1 = _current_l2(phi1, grid)
    c_shear = _current_l2(phi_shear, grid)

    current_l2_rel = float(abs(c1 - c0) / max(1e-12, abs(c0)))
    local_phase_shear_rel = float(abs(c_shear - c0) / max(1e-12, abs(c0)))

    invariance_ok = bool(current_l2_rel <= tol)
    control_ok = bool(local_phase_shear_rel > control_min)

    if not invariance_ok:
        reason = "FAIL_CURRENT_INVARIANCE_TOL"
    elif not control_ok:
        reason = "FAIL_CURRENT_CHANNEL_CONTROL_MIN"
    else:
        reason = "PASS"

    return {
        "pass": bool(reason == "PASS"),
        "reason_code": reason,
        "metrics": {
            "current_l2_rel": _q(current_l2_rel),
            "local_phase_shear_rel": _q(local_phase_shear_rel),
        },
    }


def _pair_and_localization(*, phase_reason: str, current_reason: str) -> tuple[str, str]:
    phase_pass = phase_reason == "PASS"
    current_pass = current_reason == "PASS"

    if phase_pass and current_pass:
        pair = "pass_pass"
        loc = "none"
    elif phase_pass and not current_pass:
        pair = "pass_fail"
        if current_reason == "FAIL_CURRENT_CHANNEL_CONTROL_MIN":
            loc = "toyh_observable_construction"
        else:
            loc = "c6_side_constraint"
    elif (not phase_pass) and current_pass:
        pair = "fail_pass"
        if phase_reason == "FAIL_PHASE_CHANNEL_CONTROL_MIN":
            loc = "toyh_observable_construction"
        else:
            loc = "c6_side_constraint"
    else:
        pair = "fail_fail"
        if "CONTROL" in phase_reason or "CONTROL" in current_reason:
            if "INVARIANCE" in phase_reason or "INVARIANCE" in current_reason:
                loc = "mixed"
            else:
                loc = "toyh_observable_construction"
        else:
            loc = "c6_side_constraint"

    return pair, loc


def build_bridge_toyh_c6_orthogonality_report(
    *,
    repo_root: Path,
    phase_thetas: Optional[list[float]] = None,
    grid_sizes: Optional[list[int]] = None,
    tol: float = 1e-10,
    phase_sensitive_min: float = 1e-3,
    current_control_min: float = 1e-3,
) -> dict:
    _ = repo_root

    if phase_thetas is None:
        phase_thetas = [0.0, float(np.pi / 6.0), float(np.pi / 3.0), float(np.pi / 2.0)]
    else:
        phase_thetas = list(dict.fromkeys(float(t) for t in phase_thetas))

    if grid_sizes is None:
        grid_sizes = [7, 9, 11]
    else:
        grid_sizes = list(dict.fromkeys(int(n) for n in grid_sizes))

    probes: list[dict] = []

    for theta in phase_thetas:
        for n in grid_sizes:
            probes.append(
                {
                    "probe_id": f"baseline_theta_{theta:.12g}_n_{n}",
                    "probe_kind": "baseline_global_phase",
                    "theta": float(theta),
                    "grid_n": int(n),
                    "amplitude_scale": 1.0,
                    "local_phase_shear_alpha": 0.5,
                }
            )

    # Stress probe that targets phase-channel control only.
    probes.append(
        {
            "probe_id": "stress_phase_control_small_theta_n11",
            "probe_kind": "phase_control_stress",
            "theta": 1e-6,
            "grid_n": 11,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
        }
    )

    # Stress probe that targets current-channel control only.
    probes.append(
        {
            "probe_id": "stress_current_control_small_alpha_n11",
            "probe_kind": "current_control_stress",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 1e-6,
        }
    )

    # Stress probe that intentionally breaks both invariance channels via amplitude scaling.
    probes.append(
        {
            "probe_id": "stress_c6_side_amplitude_scale_n11",
            "probe_kind": "c6_side_stress",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.1,
            "local_phase_shear_alpha": 0.5,
        }
    )

    items: list[dict] = []
    for p in probes:
        phase = _phase_channel(
            theta=float(p["theta"]),
            Nx=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            phase_sensitive_min=phase_sensitive_min,
            tol=tol,
        )
        current = _current_channel(
            theta=float(p["theta"]),
            Nx=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            local_phase_shear_alpha=float(p["local_phase_shear_alpha"]),
            control_min=current_control_min,
            tol=tol,
        )
        pair_status, localization = _pair_and_localization(
            phase_reason=str(phase["reason_code"]),
            current_reason=str(current["reason_code"]),
        )

        items.append(
            {
                "probe_id": str(p["probe_id"]),
                "probe_kind": str(p["probe_kind"]),
                "theta": _q(p["theta"]),
                "grid_n": int(p["grid_n"]),
                "amplitude_scale": _q(p["amplitude_scale"]),
                "local_phase_shear_alpha": _q(p["local_phase_shear_alpha"]),
                "phase_channel": phase,
                "current_channel": current,
                "pair_status": pair_status,
                "localization_note": localization,
            }
        )

    counts = {
        "pass_pass": sum(1 for it in items if it["pair_status"] == "pass_pass"),
        "pass_fail": sum(1 for it in items if it["pair_status"] == "pass_fail"),
        "fail_pass": sum(1 for it in items if it["pair_status"] == "fail_pass"),
        "fail_fail": sum(1 for it in items if it["pair_status"] == "fail_fail"),
    }

    localization_counts = {
        "none": sum(1 for it in items if it["localization_note"] == "none"),
        "toyh_observable_construction": sum(
            1 for it in items if it["localization_note"] == "toyh_observable_construction"
        ),
        "c6_side_constraint": sum(1 for it in items if it["localization_note"] == "c6_side_constraint"),
        "mixed": sum(1 for it in items if it["localization_note"] == "mixed"),
    }

    nonredundant = bool(counts["pass_fail"] > 0 or counts["fail_pass"] > 0)

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT",
        "bridge_family": "Toy-H_C6_multi_constraint",
        "shared_probe_set": {
            "base_thetas": [_q(t) for t in phase_thetas],
            "grid_sizes": list(grid_sizes),
            "tolerance": tol,
            "phase_channel_control_min": phase_sensitive_min,
            "current_channel_control_min": current_control_min,
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_independence.py::test_bridge_toyh_c6_orthogonality_independence",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_independence.py::test_bridge_toyh_c6_orthogonality_localization_reason_codes_are_valid",
            ]
        },
        "items": items,
        "summary": {
            "n_probes": len(items),
            "counts": counts,
            "nonredundant": nonredundant,
            "localization_counts": localization_counts,
            "localization_note": (
                "mismatch points are tagged by reason-code as C6-side constraint vs Toy-H observable construction"
            ),
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic Toy-H↔C6 orthogonality audit report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyh_c6_orthogonality_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
