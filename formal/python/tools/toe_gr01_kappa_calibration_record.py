from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np


SCHEMA = "TOE-GR-01/kappa_calibration_record/v0"
DEFAULT_DATE = "2026-02-12"
DEFAULT_POINTS = 32
DEFAULT_LENGTH = 1.0
G_N_SI = 6.67430e-11


def _sha256_json(payload: Any) -> str:
    blob = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()


def _solve_periodic_poisson(*, kappa: float, x: np.ndarray, rho: np.ndarray) -> np.ndarray:
    n = int(x.size)
    dx = float(x[1] - x[0]) if n > 1 else 1.0
    rho0 = rho - float(np.mean(rho))
    rho_hat = np.fft.fft(rho0)
    phi_hat = np.zeros_like(rho_hat, dtype=np.complex128)
    for k in range(1, n):
        lam = -4.0 * (np.sin(np.pi * k / n) ** 2) / (dx * dx)
        phi_hat[k] = (kappa * rho_hat[k]) / lam
    phi = np.fft.ifft(phi_hat).real
    phi = phi - float(np.mean(phi))
    return phi


def _laplacian_periodic(phi: np.ndarray, *, dx: float) -> np.ndarray:
    return (np.roll(phi, -1) - 2.0 * phi + np.roll(phi, 1)) / (dx * dx)


def _build_record(*, date: str, n: int, length: float, g_n_si: float) -> dict[str, Any]:
    x = np.linspace(0.0, float(length), int(n), endpoint=False, dtype=float)
    xc = 0.5 * float(length)
    sigma = 0.15 * float(length)
    rho = np.exp(-((x - xc) ** 2) / (2.0 * sigma * sigma))
    rho = rho - float(np.mean(rho))

    kappa = float(4.0 * np.pi * float(g_n_si))
    phi = _solve_periodic_poisson(kappa=kappa, x=x, rho=rho)

    dx = float(length) / float(n)
    residual = _laplacian_periodic(phi, dx=dx) - (kappa * rho)
    residual_l2 = float(np.linalg.norm(residual))
    residual_linf = float(np.max(np.abs(residual)))

    payload = {
        "schema": SCHEMA,
        "date": str(date),
        "units": {
            "phi": "m^2 s^-2",
            "rho": "kg m^-3",
            "kappa": "m^3 kg^-1 s^-2",
        },
        "params": {
            "n_points": int(n),
            "domain_length": float(length),
            "G_N": float(g_n_si),
            "kappa": float(kappa),
            "boundary": "periodic",
            "gauge": "mean(phi)=0",
        },
        "metrics": {
            "residual_l2_abs": residual_l2,
            "residual_linf_abs": residual_linf,
            "rho_mean_abs": abs(float(np.mean(rho))),
            "phi_mean_abs": abs(float(np.mean(phi))),
        },
        "x": [float(v) for v in x.tolist()],
        "rho": [float(v) for v in rho.tolist()],
        "phi": [float(v) for v in phi.tolist()],
    }
    payload["fingerprint"] = _sha256_json(payload)
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate deterministic TOE-GR-01 kappa calibration record.")
    parser.add_argument("--out", type=Path, default=Path("formal/output/toe_gr01_kappa_calibration_v0.json"))
    parser.add_argument("--date", type=str, default=DEFAULT_DATE)
    parser.add_argument("--n-points", type=int, default=DEFAULT_POINTS)
    parser.add_argument("--length", type=float, default=DEFAULT_LENGTH)
    parser.add_argument("--g-n", type=float, default=G_N_SI)
    args = parser.parse_args()

    record = _build_record(date=args.date, n=args.n_points, length=args.length, g_n_si=args.g_n)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.out.as_posix())
    print(record["fingerprint"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
