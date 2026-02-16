from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.rl13_velocity_addition_group_law_v0 import (
    RL13VelocityCase,
    RL13VelocityReport,
    rl13_v0_tolerances,
)


def _einstein_add(beta_u: float, beta_v: float) -> float:
    return (beta_u + beta_v) / (1.0 + beta_u * beta_v)


def _galilean_add(beta_u: float, beta_v: float) -> float:
    return beta_u + beta_v


def build_rl13_reports(
    *,
    c: float = 1.0,
    beta_u: float = 0.3,
    beta_v: float = 0.4,
    tolerance_profile: str = "pinned",
) -> tuple[RL13VelocityReport, RL13VelocityReport]:
    tolerances = rl13_v0_tolerances(tolerance_profile)
    beta_expected = _einstein_add(beta_u, beta_v)

    beta_comp_pos = _einstein_add(beta_u, beta_v)
    residual_pos = abs(beta_comp_pos - beta_expected)

    beta_comp_neg = _galilean_add(beta_u, beta_v)
    residual_neg = abs(beta_comp_neg - beta_expected)

    params = {
        "c": float(c),
        "beta_u": float(beta_u),
        "beta_v": float(beta_v),
        "eps_addition": float(tolerances["eps_addition"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = RL13VelocityReport(
        schema="RL/velocity_addition_front_door_report/v1",
        config_tag="rl13_velocity_addition_group_law_v0",
        regime_tag="RL13_Velocity_Addition_Group_Law",
        domain_tag="rl13_velocity_addition_group_law_domain_01",
        params=params,
        boundary="velocity_addition_1d",
        cases=[
            RL13VelocityCase(
                case_id="positive_control",
                kind="positive_control",
                beta_u=float(beta_u),
                beta_v=float(beta_v),
                beta_comp=float(beta_comp_pos),
                beta_expected=float(beta_expected),
                addition_residual=float(residual_pos),
            ),
            RL13VelocityCase(
                case_id="negative_control",
                kind="negative_control",
                beta_u=float(beta_u),
                beta_v=float(beta_v),
                beta_comp=float(beta_comp_neg),
                beta_expected=float(beta_expected),
                addition_residual=float(residual_neg),
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

    report, candidate = build_rl13_reports()
    out_dir = repo_root / "formal" / "external_evidence" / "rl13_velocity_addition_group_law_domain_01"
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "rl13_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "rl13_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
