from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.rl14_time_dilation_proxy_v0 import (
    RL14DilationCase,
    RL14DilationReport,
    rl14_v0_tolerances,
)


def _gamma(beta: float) -> float:
    return 1.0 / (1.0 - beta**2) ** 0.5


def build_rl14_reports(
    *,
    c: float = 1.0,
    beta: float = 0.6,
    delta_t: float = 2.0,
    tolerance_profile: str = "pinned",
) -> tuple[RL14DilationReport, RL14DilationReport]:
    tolerances = rl14_v0_tolerances(tolerance_profile)
    gamma = _gamma(beta)
    expected_ratio = 1.0 / gamma

    delta_tau_pos = delta_t / gamma
    ratio_pos = delta_tau_pos / delta_t
    residual_pos = abs(ratio_pos - expected_ratio)

    delta_tau_neg = delta_t
    ratio_neg = delta_tau_neg / delta_t
    residual_neg = abs(ratio_neg - expected_ratio)

    params = {
        "c": float(c),
        "beta": float(beta),
        "gamma": float(gamma),
        "delta_t": float(delta_t),
        "eps_dilation": float(tolerances["eps_dilation"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = RL14DilationReport(
        schema="RL/time_dilation_front_door_report/v1",
        config_tag="rl14_time_dilation_proxy_v0",
        regime_tag="RL14_Time_Dilation_Proxy",
        domain_tag="rl14_time_dilation_proxy_domain_01",
        params=params,
        boundary="time_dilation_1d",
        cases=[
            RL14DilationCase(
                case_id="positive_control",
                kind="positive_control",
                beta=float(beta),
                gamma=float(gamma),
                delta_t=float(delta_t),
                delta_tau=float(delta_tau_pos),
                dilation_ratio=float(ratio_pos),
                dilation_residual=float(residual_pos),
            ),
            RL14DilationCase(
                case_id="negative_control",
                kind="negative_control",
                beta=float(beta),
                gamma=float(gamma),
                delta_t=float(delta_t),
                delta_tau=float(delta_tau_neg),
                dilation_ratio=float(ratio_neg),
                dilation_residual=float(residual_neg),
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

    report, candidate = build_rl14_reports()
    out_dir = repo_root / "formal" / "external_evidence" / "rl14_time_dilation_proxy_domain_01"
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "rl14_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "rl14_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
