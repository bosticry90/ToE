"""OV-UCFF-01: UCFF jitter-structure audit scaffold.

This module provides a deterministic, quarantine-safe audit scaffold for
"UCFF-like" dispersion bookkeeping under small parameter jitter.

What it does
- Defines a simple polynomial dispersion template (symbolic) consistent with a
  UCFF/Bogoliubov-style ω²(k) expansion including k², k⁴, and optional k⁶.
- Runs a deterministic numeric scan under small multiplicative jitter to check
  that ω²(k) remains non-negative over a chosen k-grid.

Policy / limits
- Not an empirical anchor.
- Not a claim that UCFF is correct physics; this is a software/audit harness.
- The numeric scan is a *demo* stability check for a chosen parameter set and
  a chosen k-window; it does not establish global stability.

Rationale
The legacy archive contains UCFF symbolic roundtrip tests. A low-risk next port
is to create a front-door audit harness that records structural properties and
produces a frozen diagnostic artifact, without importing legacy code directly.
"""

from __future__ import annotations

from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np
import sympy as sp


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


def ucff_symbolic_symbols() -> dict[str, sp.Symbol]:
    # k, omega are treated as symbols; we work at the ω²(k) level.
    k = sp.Symbol("k", real=True)
    omega = sp.Symbol("omega", real=True)

    # Parameters
    rho0 = sp.Symbol("rho0", real=True)
    g = sp.Symbol("g", real=True)
    lam = sp.Symbol("lam", real=True)
    beta = sp.Symbol("beta", real=True)

    return {"k": k, "omega": omega, "rho0": rho0, "g": g, "lam": lam, "beta": beta}


def ucff_dispersion_omega2_first_order() -> sp.Expr:
    s = ucff_symbolic_symbols()
    k = s["k"]
    rho0 = s["rho0"]
    g = s["g"]
    lam = s["lam"]

    # ω² = (k²/2)² + (g ρ0) k² + lam k⁴
    return (k**2 / 2) ** 2 + (g * rho0) * k**2 + lam * k**4


def ucff_dispersion_omega2_second_order() -> sp.Expr:
    s = ucff_symbolic_symbols()
    k = s["k"]
    beta = s["beta"]
    return ucff_dispersion_omega2_first_order() + beta * k**6


def ucff_first_order_lagrangian_contains_coherence_density_term() -> bool:
    """Structural check: include lam * (rho_x)^2 / (4 rho).

    This is not the full UCFF Lagrangian; it is the minimal structure used for
    audit purposes.
    """

    x = sp.Symbol("x", real=True)
    rho = sp.Symbol("rho", positive=True, real=True)
    lam = ucff_symbolic_symbols()["lam"]
    rho_x = sp.diff(rho, x)

    L = lam * (rho_x**2) / (4 * rho)

    return bool(L.has(lam) and L.has(rho_x**2) and L.has(1 / rho))


@dataclass(frozen=True)
class OVUCFF01JitterStructureReport:
    schema: str
    config_tag: str
    seed: int
    n_jitters: int
    jitter_frac: float
    k_max: float
    n_k: int
    params_baseline: dict[str, float]
    symbolic_structure: dict[str, bool]
    min_omega2_over_grid_baseline: float
    min_omega2_over_grid_min_across_jitters: float
    n_stable: int
    n_unstable: int

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def _omega2_numeric(
    *,
    k: np.ndarray,
    rho0: float,
    g: float,
    lam: float,
    beta: float,
) -> np.ndarray:
    k = np.asarray(k, dtype=float)
    omega2 = (k**2 / 2.0) ** 2 + (g * rho0) * (k**2) + lam * (k**4) + beta * (k**6)
    return omega2


def ovucff01_jitter_structure_audit(
    *,
    seed: int = 12345,
    n_jitters: int = 64,
    jitter_frac: float = 0.02,
    k_max: float = 6.0,
    n_k: int = 241,
    rho0: float = 1.0,
    g: float = 1.0,
    lam: float = 0.10,
    beta: float = 0.01,
    config_tag: str = "OV-UCFF-01_jitter_structure_v1",
) -> OVUCFF01JitterStructureReport:
    if n_jitters < 0:
        raise ValueError("n_jitters must be >= 0")
    if not (0.0 <= jitter_frac <= 1.0):
        raise ValueError("jitter_frac must be in [0, 1]")
    if k_max <= 0:
        raise ValueError("k_max must be > 0")
    if n_k < 3:
        raise ValueError("n_k must be >= 3")

    k = np.linspace(0.0, float(k_max), int(n_k))

    # Symbolic structure checks.
    s = ucff_symbolic_symbols()
    k_sym = s["k"]

    omega2_1 = sp.expand(ucff_dispersion_omega2_first_order())
    omega2_2 = sp.expand(ucff_dispersion_omega2_second_order())

    structure = {
        "first_order_has_k2": bool(omega2_1.has(k_sym**2)),
        "first_order_has_k4": bool(omega2_1.has(k_sym**4)),
        "first_order_has_k6": bool(omega2_1.has(k_sym**6)),
        "second_order_has_k2": bool(omega2_2.has(k_sym**2)),
        "second_order_has_k4": bool(omega2_2.has(k_sym**4)),
        "second_order_has_k6": bool(omega2_2.has(k_sym**6)),
        "lagrangian_contains_coherence_density_term": bool(ucff_first_order_lagrangian_contains_coherence_density_term()),
    }

    baseline_min = float(np.min(_omega2_numeric(k=k, rho0=float(rho0), g=float(g), lam=float(lam), beta=float(beta))))

    rng = np.random.default_rng(int(seed))
    n_stable = 0
    n_unstable = 0
    min_across = baseline_min

    eps = 1e-12
    for _ in range(int(n_jitters)):
        # Multiplicative jitter on each parameter. (rho0, g, lam, beta)
        # We keep the audit deterministic by fixed RNG seed and ordering.
        j = rng.normal(0.0, float(jitter_frac), size=4)
        rho0_j = float(rho0) * (1.0 + float(j[0]))
        g_j = float(g) * (1.0 + float(j[1]))
        lam_j = float(lam) * (1.0 + float(j[2]))
        beta_j = float(beta) * (1.0 + float(j[3]))

        m = float(np.min(_omega2_numeric(k=k, rho0=rho0_j, g=g_j, lam=lam_j, beta=beta_j)))
        min_across = float(min(min_across, m))

        if m >= -eps:
            n_stable += 1
        else:
            n_unstable += 1

    return OVUCFF01JitterStructureReport(
        schema="OV-UCFF-01/jitter_structure_report/v1",
        config_tag=str(config_tag),
        seed=int(seed),
        n_jitters=int(n_jitters),
        jitter_frac=float(jitter_frac),
        k_max=float(k_max),
        n_k=int(n_k),
        params_baseline={
            "rho0": float(rho0),
            "g": float(g),
            "lam": float(lam),
            "beta": float(beta),
        },
        symbolic_structure=dict(structure),
        min_omega2_over_grid_baseline=float(baseline_min),
        min_omega2_over_grid_min_across_jitters=float(min_across),
        n_stable=int(n_stable),
        n_unstable=int(n_unstable),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-UCFF-01" / "ucff_jitter_structure.json"


def write_ovucff01_jitter_structure_artifact(
    *,
    path: Path | None = None,
    seed: int = 12345,
    n_jitters: int = 64,
    jitter_frac: float = 0.02,
    k_max: float = 6.0,
    n_k: int = 241,
) -> Path:
    rep = ovucff01_jitter_structure_audit(
        seed=int(seed),
        n_jitters=int(n_jitters),
        jitter_frac=float(jitter_frac),
        k_max=float(k_max),
        n_k=int(n_k),
    )

    payload = {
        "schema": "OV-UCFF-01/jitter_structure_artifact/v1",
        "notes": (
            "Deterministic UCFF dispersion jitter-structure demo only; not external evidence and not a physics claim. "
            "Records symbolic term-presence checks and a bounded numeric non-negativity scan over a chosen k-window."
        ),
        "report": rep.to_jsonable(),
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
