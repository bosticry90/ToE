from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.rl12_lorentz_poincare_invariance_proxy_v0 import (
    RL12LorentzCase,
    RL12LorentzReport,
    rl12_v0_tolerances,
)


def _invariant_field(x: np.ndarray, t: np.ndarray, sigma: float) -> np.ndarray:
    s2 = t**2 - x**2
    return np.exp(-((s2**2) / (sigma**2)))


def _noninvariant_field(x: np.ndarray, t: np.ndarray, sigma: float) -> np.ndarray:
    s2 = t**2 + x**2
    return np.exp(-((s2**2) / (sigma**2)))


def _lorentz_boost(x: np.ndarray, t: np.ndarray, beta: float, c: float) -> tuple[np.ndarray, np.ndarray]:
    gamma = 1.0 / np.sqrt(1.0 - beta**2)
    x_prime = gamma * (x - beta * c * t)
    t_prime = gamma * (t - (beta * x) / c)
    return x_prime, t_prime


def _relative_l2(u: np.ndarray, v: np.ndarray) -> float:
    diff = np.linalg.norm(u - v)
    denom = np.linalg.norm(u)
    return float(diff / max(denom, 1e-12))


def build_rl12_reports(
    *,
    length: float = 8.0,
    time_window: float = 6.0,
    nx: int = 256,
    nt: int = 128,
    c: float = 1.0,
    beta: float = 0.3,
    boundary: str = "finite",
    sigma: float = 6.0,
    tolerance_profile: str = "pinned",
) -> tuple[RL12LorentzReport, RL12LorentzReport]:
    dx = length / float(nx)
    dt = time_window / float(nt)
    x = np.linspace(-0.5 * length, 0.5 * length, nx, endpoint=False)
    t = np.linspace(0.0, time_window, nt, endpoint=False)
    X, T = np.meshgrid(x, t, indexing="xy")

    x_prime, t_prime = _lorentz_boost(X, T, beta, c)

    tolerances = rl12_v0_tolerances(tolerance_profile)
    params = {
        "length": float(length),
        "time_window": float(time_window),
        "nx": float(nx),
        "nt": float(nt),
        "dx": float(dx),
        "dt": float(dt),
        "c": float(c),
        "beta": float(beta),
        "gamma": float(1.0 / np.sqrt(1.0 - beta**2)),
        "eps_invariant": float(tolerances["eps_invariant"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    u_pos = _invariant_field(X, T, sigma)
    u_pos_boosted = _invariant_field(x_prime, t_prime, sigma)
    metric_pos = _relative_l2(u_pos, u_pos_boosted)

    u_neg = _noninvariant_field(X, T, sigma)
    u_neg_boosted = _noninvariant_field(x_prime, t_prime, sigma)
    metric_neg = _relative_l2(u_neg, u_neg_boosted)

    report = RL12LorentzReport(
        schema="RL/lorentz_poincare_invariance_front_door_report/v1",
        config_tag="rl12_lorentz_poincare_invariance_proxy_v0",
        regime_tag="RL12_Lorentz_Poincare_Invariance_Proxy",
        domain_tag="rl12_lorentz_poincare_invariance_proxy_domain_01",
        params=params,
        boundary=str(boundary),
        x=[float(v) for v in x.tolist()],
        t=[float(v) for v in t.tolist()],
        cases=[
            RL12LorentzCase(
                case_id="positive_control",
                kind="positive_control",
                invariant_metric=float(metric_pos),
                u=[float(v) for v in u_pos.reshape(-1).tolist()],
                u_boosted=[float(v) for v in u_pos_boosted.reshape(-1).tolist()],
            ),
            RL12LorentzCase(
                case_id="negative_control",
                kind="negative_control",
                invariant_metric=float(metric_neg),
                u=[float(v) for v in u_neg.reshape(-1).tolist()],
                u_boosted=[float(v) for v in u_neg_boosted.reshape(-1).tolist()],
            ),
        ],
    )

    return report, report


def main() -> None:
    repo_root = Path(__file__).resolve()
    while repo_root != repo_root.parent:
        if (repo_root / "formal").exists():
            break
        repo_root = repo_root.parent
    else:
        raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")

    report, candidate = build_rl12_reports()
    out_dir = repo_root / "formal" / "external_evidence" / "rl12_lorentz_poincare_invariance_proxy_domain_01"
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "rl12_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "rl12_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
