"""OV-MB-01: Orthogonality catastrophe trend audit (toy model scaffold).

This is a minimal many-body audit intended to capture the *trend* that an
infinite Fermi sea becomes orthogonal under a local perturbation.

We use a 1D tight-binding ring (free fermions) with a single-site impurity.
The many-body ground state is a Slater determinant of occupied single-particle
orbitals, so the overlap reduces to a determinant of the occupied-orbital
overlap matrix.

Notes
-----
- This is a numerical trend audit, not an empirical anchor.
- It is deliberately small and fast (finite-size systems only).
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


def _tight_binding_ring_hamiltonian(*, L: int, t: float = 1.0) -> np.ndarray:
    if L < 4:
        raise ValueError("L must be >= 4")
    H = np.zeros((L, L), dtype=float)
    for i in range(L):
        j = (i + 1) % L
        H[i, j] = -float(t)
        H[j, i] = -float(t)
    return H


def _with_impurity(H: np.ndarray, *, V: float, site: int = 0) -> np.ndarray:
    H2 = np.array(H, copy=True)
    H2[int(site), int(site)] += float(V)
    return H2


def _occupied_orbitals(*, H: np.ndarray, n_occ: int) -> np.ndarray:
    # Columns are eigenvectors.
    evals, evecs = np.linalg.eigh(H)
    idx = np.argsort(evals)
    evecs = evecs[:, idx]
    return evecs[:, : int(n_occ)]


def slater_overlap_determinant(*, Psi0: np.ndarray, Psi1: np.ndarray) -> float:
    """Return |det(Psi0^T Psi1)| for real orbitals."""

    S = Psi0.T @ Psi1
    det = np.linalg.det(S)
    return float(abs(det))


@dataclass(frozen=True)
class OVMB01OrthogonalityTrendPoint:
    L: int
    n_occ: int
    overlap: float


@dataclass(frozen=True)
class OVMB01OrthogonalityTrendReport:
    schema: str
    config_tag: str
    filling: float
    t: float
    V: float
    points: tuple[OVMB01OrthogonalityTrendPoint, ...]

    def to_jsonable_without_fingerprint(self) -> dict[str, object]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, object]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovmb01_orthogonality_trend_audit(
    *,
    L_values: tuple[int, ...],
    filling: float = 0.25,
    t: float = 1.0,
    V: float = 1.0,
    config_tag: str = "OV-MB-01_orthogonality_trend_v1",
) -> OVMB01OrthogonalityTrendReport:
    """Compute the many-body ground-state overlap vs system size."""

    if not (0.0 < filling < 1.0):
        raise ValueError("filling must be in (0, 1)")

    pts: list[OVMB01OrthogonalityTrendPoint] = []

    for L in L_values:
        n_occ = max(1, int(round(float(L) * float(filling))))
        H0 = _tight_binding_ring_hamiltonian(L=int(L), t=float(t))
        H1 = _with_impurity(H0, V=float(V), site=0)

        Psi0 = _occupied_orbitals(H=H0, n_occ=n_occ)
        Psi1 = _occupied_orbitals(H=H1, n_occ=n_occ)

        ov = slater_overlap_determinant(Psi0=Psi0, Psi1=Psi1)
        pts.append(OVMB01OrthogonalityTrendPoint(L=int(L), n_occ=int(n_occ), overlap=float(ov)))

    return OVMB01OrthogonalityTrendReport(
        schema="OV-MB-01/orthogonality_trend_report/v1",
        config_tag=str(config_tag),
        filling=float(filling),
        t=float(t),
        V=float(V),
        points=tuple(pts),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-MB-01" / "orthogonality_trend.json"


def write_ovmb01_orthogonality_trend_artifact(
    *,
    path: Path | None = None,
    L_values: tuple[int, ...] = (8, 12, 16, 20, 24, 28, 32),
    filling: float = 0.25,
    t: float = 1.0,
    V: float = 1.0,
) -> Path:
    rec = ovmb01_orthogonality_trend_audit(
        L_values=tuple(int(x) for x in L_values),
        filling=float(filling),
        t=float(t),
        V=float(V),
    )
    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8")
    return out
