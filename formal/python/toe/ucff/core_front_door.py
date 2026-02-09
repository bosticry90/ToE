from __future__ import annotations

from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
from typing import Any, Dict, List

import numpy as np


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class UcffCoreParams:
    """UCFF core parameters for the dispersion polynomial.

    Notes
    - This is a *bookkeeping* front door, not a physics claim.
    - Parameters are carried through verbatim in the report.
    """

    rho0: float = 1.0
    g: float = 0.0
    lam: float = 0.0
    beta: float = 0.0


@dataclass(frozen=True)
class UcffCoreInput:
    """Typed UCFF core input.

    Policy
    - No implicit file I/O.
    - Deterministic outputs for the same inputs.
    """

    k: List[float]
    params: UcffCoreParams
    config_tag: str = "UCFF/core_front_door_report/v1"


@dataclass(frozen=True)
class UcffCoreReport:
    schema: str
    config_tag: str
    params: Dict[str, float]
    k: List[float]
    omega2: List[float]

    def to_jsonable_without_fingerprint(self) -> Dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> Dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ucff_dispersion_omega2_numeric(*, k: np.ndarray, params: UcffCoreParams) -> np.ndarray:
    """Compute UCFF-like ω²(k) polynomial.

    Form (bookkeeping):
      ω² = (k²/2)² + (g ρ0) k² + lam k⁴ + beta k⁶

    This mirrors the UCFF audit scaffolds and provides a minimal non-archive
    core surface suitable for deterministic regression locks.
    """

    k = np.asarray(k, dtype=float)
    omega2 = (k**2 / 2.0) ** 2 + (float(params.g) * float(params.rho0)) * (k**2) + float(params.lam) * (k**4) + float(
        params.beta
    ) * (k**6)
    return omega2


def ucff_core_report(inp: UcffCoreInput) -> UcffCoreReport:
    k = np.asarray(list(inp.k), dtype=float)
    omega2 = ucff_dispersion_omega2_numeric(k=k, params=inp.params)

    return UcffCoreReport(
        schema="UCFF/core_front_door_report/v1",
        config_tag=str(inp.config_tag),
        params={
            "rho0": float(inp.params.rho0),
            "g": float(inp.params.g),
            "lam": float(inp.params.lam),
            "beta": float(inp.params.beta),
        },
        k=[float(x) for x in k.tolist()],
        omega2=[float(x) for x in omega2.tolist()],
    )


def dumps_ucff_core_report(report: UcffCoreReport) -> str:
    """Deterministic JSON serialization."""

    return json.dumps(report.to_jsonable(), indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def loads_ucff_core_report(text: str) -> Dict[str, Any]:
    payload = json.loads(text)
    if payload.get("schema") != "UCFF/core_front_door_report/v1":
        raise ValueError(f"Unexpected schema: {payload.get('schema')!r}")
    return payload
