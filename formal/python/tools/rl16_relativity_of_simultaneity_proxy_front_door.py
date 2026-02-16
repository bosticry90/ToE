from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.rl16_relativity_of_simultaneity_proxy_v0 import (
    RL16SimultaneityCase,
    RL16SimultaneityReport,
    rl16_v0_tolerances,
)


def _gamma(beta: float) -> float:
    return 1.0 / (1.0 - beta**2) ** 0.5


def build_rl16_reports(
    *,
    c: float = 1.0,
    beta: float = 0.6,
    delta_t: float = 0.2,
    delta_x: float = 1.5,
    tolerance_profile: str = "pinned",
) -> tuple[RL16SimultaneityReport, RL16SimultaneityReport]:
    tolerances = rl16_v0_tolerances(tolerance_profile)
    gamma = _gamma(beta)
    expected_delta_t_prime = gamma * (delta_t - beta * delta_x / c)

    delta_t_prime_pos = expected_delta_t_prime
    residual_pos = abs(delta_t_prime_pos - expected_delta_t_prime)

    delta_t_prime_neg = delta_t
    residual_neg = abs(delta_t_prime_neg - expected_delta_t_prime)

    params = {
        "c": float(c),
        "beta": float(beta),
        "gamma": float(gamma),
        "delta_t": float(delta_t),
        "delta_x": float(delta_x),
        "eps_simultaneity": float(tolerances["eps_simultaneity"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = RL16SimultaneityReport(
        schema="RL/relativity_of_simultaneity_front_door_report/v1",
        config_tag="rl16_relativity_of_simultaneity_proxy_v0",
        regime_tag="RL16_Relativity_Of_Simultaneity_Proxy",
        domain_tag="rl16_relativity_of_simultaneity_proxy_domain_01",
        params=params,
        boundary="relativity_of_simultaneity_1d",
        cases=[
            RL16SimultaneityCase(
                case_id="positive_control",
                kind="positive_control",
                beta=float(beta),
                gamma=float(gamma),
                delta_t=float(delta_t),
                delta_x=float(delta_x),
                delta_t_prime=float(delta_t_prime_pos),
                simultaneity_residual=float(residual_pos),
            ),
            RL16SimultaneityCase(
                case_id="negative_control",
                kind="negative_control",
                beta=float(beta),
                gamma=float(gamma),
                delta_t=float(delta_t),
                delta_x=float(delta_x),
                delta_t_prime=float(delta_t_prime_neg),
                simultaneity_residual=float(residual_neg),
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

    report, candidate = build_rl16_reports()
    out_dir = repo_root / "formal" / "external_evidence" / "rl16_relativity_of_simultaneity_proxy_domain_01"
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "rl16_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "rl16_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
