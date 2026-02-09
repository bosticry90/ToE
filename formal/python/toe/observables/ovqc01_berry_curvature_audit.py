"""OV-QC-01: Berry curvature / Chern number audit (two-band scaffold).

This module provides a minimal, deterministic computation of the Chern number
for a 2D two-band lattice Hamiltonian using the Fukui-Hatsugai-Suzuki (FHS)
link-variable discretization.

It is intended as an internal consistency scaffold for exploring quantum
geometric effects (Berry curvature / quantum metric) in simplified models.

Notes
-----
- This is a mathematical audit; it is not an empirical anchor.
- It does not assume EWT contains a specific lattice Hamiltonian; it just
  provides a robust computational primitive to attach to future bridge models.
"""

from __future__ import annotations

from dataclasses import dataclass
from dataclasses import asdict
import hashlib
import json
from pathlib import Path

import numpy as np


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


@dataclass(frozen=True)
class OVQC01ChernReport:
    schema: str
    config_tag: str
    model: str
    m: float
    grid_n: int
    chern_number: int

    def to_jsonable_without_fingerprint(self) -> dict[str, object]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, object]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def _occupied_eigenvector(H: np.ndarray) -> np.ndarray:
    # Return the eigenvector for the lowest eigenvalue.
    evals, evecs = np.linalg.eigh(H)
    idx = int(np.argmin(evals))
    v = evecs[:, idx]
    # Fix an arbitrary phase convention to reduce numerical noise.
    # (Not strictly required for FHS, but improves determinism.)
    phase = v[0] / abs(v[0]) if abs(v[0]) > 0 else 1.0 + 0.0j
    return v / phase


def _link(u: np.ndarray, v: np.ndarray) -> complex:
    z = np.vdot(u, v)
    if abs(z) == 0:
        # Degeneracy or numerical failure.
        return 1.0 + 0.0j
    return z / abs(z)


def qiwuzhang_hamiltonian(*, kx: float, ky: float, m: float) -> np.ndarray:
    """Qi-Wu-Zhang Chern insulator model.

    d = (sin kx, sin ky, m + cos kx + cos ky)
    H = d · sigma
    """

    sx = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=complex)
    sy = np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=complex)
    sz = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=complex)

    dx = np.sin(kx)
    dy = np.sin(ky)
    dz = float(m) + np.cos(kx) + np.cos(ky)

    return dx * sx + dy * sy + dz * sz


def ovqc01_chern_number_qiwuzhang(
    *,
    m: float,
    grid_n: int = 21,
    config_tag: str = "OV-QC-01_chern_qiwuzhang_v1",
) -> OVQC01ChernReport:
    """Compute Chern number for the occupied band of the QWZ model."""

    if grid_n < 5:
        raise ValueError("grid_n must be >= 5")

    # kx, ky in [-pi, pi)
    ks = np.linspace(-np.pi, np.pi, num=grid_n, endpoint=False)

    # Store occupied eigenvectors on grid.
    psi = np.zeros((grid_n, grid_n, 2), dtype=complex)
    for ix, kx in enumerate(ks):
        for iy, ky in enumerate(ks):
            H = qiwuzhang_hamiltonian(kx=float(kx), ky=float(ky), m=float(m))
            psi[ix, iy, :] = _occupied_eigenvector(H)

    # Link variables Ux, Uy.
    Ux = np.zeros((grid_n, grid_n), dtype=complex)
    Uy = np.zeros((grid_n, grid_n), dtype=complex)

    for ix in range(grid_n):
        for iy in range(grid_n):
            u = psi[ix, iy]
            v_x = psi[(ix + 1) % grid_n, iy]
            v_y = psi[ix, (iy + 1) % grid_n]
            Ux[ix, iy] = _link(u, v_x)
            Uy[ix, iy] = _link(u, v_y)

    # Berry flux per plaquette.
    flux = 0.0
    for ix in range(grid_n):
        for iy in range(grid_n):
            # Ux(i,j) Uy(i+1,j) / (Ux(i,j+1) Uy(i,j))
            z = Ux[ix, iy] * Uy[(ix + 1) % grid_n, iy] / (Ux[ix, (iy + 1) % grid_n] * Uy[ix, iy])
            flux += np.angle(z)

    chern = int(np.rint(flux / (2.0 * np.pi)))

    return OVQC01ChernReport(
        schema="OV-QC-01/chern_report/v1",
        config_tag=str(config_tag),
        model="qiwuzhang",
        m=float(m),
        grid_n=int(grid_n),
        chern_number=int(chern),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-QC-01" / "chern_qiwuzhang.json"


def write_ovqc01_chern_qiwuzhang_artifact(*, path: Path | None = None, m: float = -1.0, grid_n: int = 25) -> Path:
    rec = ovqc01_chern_number_qiwuzhang(m=float(m), grid_n=int(grid_n))
    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8")
    return out
