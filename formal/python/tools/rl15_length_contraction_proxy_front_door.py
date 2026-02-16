from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.rl15_length_contraction_proxy_v0 import (
    RL15ContractionCase,
    RL15ContractionReport,
    rl15_v0_tolerances,
)


def _gamma(beta: float) -> float:
    return 1.0 / (1.0 - beta**2) ** 0.5


def build_rl15_reports(
    *,
    c: float = 1.0,
    beta: float = 0.6,
    L0: float = 2.0,
    tolerance_profile: str = "pinned",
) -> tuple[RL15ContractionReport, RL15ContractionReport]:
    tolerances = rl15_v0_tolerances(tolerance_profile)
    gamma = _gamma(beta)
    expected_ratio = 1.0 / gamma

    L_pos = L0 / gamma
    ratio_pos = L_pos / L0
    residual_pos = abs(ratio_pos - expected_ratio)

    L_neg = L0
    ratio_neg = L_neg / L0
    residual_neg = abs(ratio_neg - expected_ratio)

    params = {
        "c": float(c),
        "beta": float(beta),
        "gamma": float(gamma),
        "L0": float(L0),
        "eps_contraction": float(tolerances["eps_contraction"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = RL15ContractionReport(
        schema="RL/length_contraction_front_door_report/v1",
        config_tag="rl15_length_contraction_proxy_v0",
        regime_tag="RL15_Length_Contraction_Proxy",
        domain_tag="rl15_length_contraction_proxy_domain_01",
        params=params,
        boundary="length_contraction_1d",
        cases=[
            RL15ContractionCase(
                case_id="positive_control",
                kind="positive_control",
                beta=float(beta),
                gamma=float(gamma),
                L0=float(L0),
                L=float(L_pos),
                contraction_ratio=float(ratio_pos),
                contraction_residual=float(residual_pos),
            ),
            RL15ContractionCase(
                case_id="negative_control",
                kind="negative_control",
                beta=float(beta),
                gamma=float(gamma),
                L0=float(L0),
                L=float(L_neg),
                contraction_ratio=float(ratio_neg),
                contraction_residual=float(residual_neg),
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

    report, candidate = build_rl15_reports()
    out_dir = repo_root / "formal" / "external_evidence" / "rl15_length_contraction_proxy_domain_01"
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "rl15_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "rl15_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
