"""OV-FG-01: Graph/Fourier mode consistency audit (scaffold).

This audit is a *structural cross-check* that connects:
- continuous Fourier-mode reasoning (periodic domain), and
- discrete graph/lattice reasoning (ring graph Laplacian eigenmodes).

It is not an external empirical anchor. It is an internal consistency/hygiene
check intended to surface hidden continuum-limit assumptions.

Notes
-----
- Uses a simple ring graph because its eigenmodes are analytically known.
- Intended usage is to extend/replace the operator under test as the ToE
  pipeline grows.
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


def ring_graph_laplacian(*, n: int, dx: float = 1.0) -> np.ndarray:
    """Return the 1D ring graph Laplacian approximating -∂xx.

    We use the standard second-difference with periodic boundary conditions:
        (L f)_i = (2 f_i - f_{i-1} - f_{i+1}) / dx^2

    This is a positive semidefinite operator corresponding to -d^2/dx^2.
    """

    if n < 3:
        raise ValueError("n must be >= 3")
    if dx <= 0:
        raise ValueError("dx must be > 0")

    L = np.zeros((n, n), dtype=float)
    for i in range(n):
        L[i, i] = 2.0
        L[i, (i - 1) % n] = -1.0
        L[i, (i + 1) % n] = -1.0
    return L / (dx * dx)


def discrete_fourier_mode(*, n: int, m: int) -> np.ndarray:
    """Complex-valued discrete Fourier mode on a ring.

    m indexes the mode: k = 2π m / (n dx) in the continuum interpretation.
    """

    j = np.arange(n)
    return np.exp(2j * np.pi * m * j / n)


def ring_graph_laplacian_eigenvalue(*, n: int, m: int, dx: float = 1.0) -> float:
    """Closed-form eigenvalue for mode m on a ring graph Laplacian."""

    theta = 2.0 * np.pi * m / n
    lam = (2.0 - 2.0 * np.cos(theta)) / (dx * dx)
    return float(lam)


@dataclass(frozen=True)
class OVFG01GraphFourierModeAuditReport:
    schema: str
    n: int
    dx: float
    mode_m: int
    eigenvalue_expected: float
    eigenvalue_observed: float
    mode_purity_l2_error: float

    def to_jsonable_without_fingerprint(self) -> dict[str, object]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, object]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovfg01_graph_fourier_mode_audit(*, n: int, dx: float, mode_m: int) -> OVFG01GraphFourierModeAuditReport:
    """Check that a discrete Fourier mode is (numerically) an eigenvector of the ring Laplacian."""

    L = ring_graph_laplacian(n=n, dx=dx)
    v = discrete_fourier_mode(n=n, m=mode_m)

    Lv = L @ v

    # Rayleigh quotient for observed eigenvalue.
    denom = np.vdot(v, v)
    if denom == 0:
        raise RuntimeError("unexpected zero-norm mode")
    lam_obs = np.vdot(v, Lv) / denom

    lam_exp = ring_graph_laplacian_eigenvalue(n=n, m=mode_m, dx=dx)

    # Purity: how close is Lv to lam*v?
    err = np.linalg.norm(Lv - lam_exp * v) / np.linalg.norm(v)

    return OVFG01GraphFourierModeAuditReport(
        schema="OV-FG-01/graph_fourier_mode_audit_report/v1",
        n=int(n),
        dx=float(dx),
        mode_m=int(mode_m),
        eigenvalue_expected=float(lam_exp),
        eigenvalue_observed=float(np.real(lam_obs)),
        mode_purity_l2_error=float(np.real(err)),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-FG-01" / "ring_graph_fourier_mode_audit.json"


def write_ovfg01_graph_fourier_mode_audit_artifact(
    *,
    path: Path | None = None,
    n: int = 32,
    dx: float = 0.5,
    mode_m: int = 3,
) -> Path:
    rec = ovfg01_graph_fourier_mode_audit(n=int(n), dx=float(dx), mode_m=int(mode_m))
    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8")
    return out
