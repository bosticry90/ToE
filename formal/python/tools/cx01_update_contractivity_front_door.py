from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.cx01_update_contractivity_v0 import (
    CX01ContractivityCase,
    CX01ContractivityReport,
    cx01_v0_tolerances,
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "cx01_update_contractivity_domain_01"


def _initial_pair(*, state_dim: int) -> tuple[np.ndarray, np.ndarray]:
    idx = np.arange(int(state_dim), dtype=float)
    x0 = np.cos(idx) + 0.1 * idx
    y0 = np.sin(idx) - 0.05 * idx
    return x0, y0


def _contractivity_metrics(
    *,
    x0: np.ndarray,
    y0: np.ndarray,
    contraction_factor_per_step: float,
    steps: int,
) -> tuple[float, float, float]:
    distance_in = float(np.linalg.norm(x0 - y0))
    scale_total = abs(float(contraction_factor_per_step)) ** int(steps)
    x_t = scale_total * x0
    y_t = scale_total * y0
    distance_out = float(np.linalg.norm(x_t - y_t))
    empirical = float(distance_out / distance_in) if distance_in > 0.0 else 0.0
    return distance_in, distance_out, empirical


def build_cx01_reports(
    *,
    state_dim: int = 3,
    steps: int = 3,
    k_contract: float = 0.8,
    k_break: float = 1.05,
    tolerance_profile: str = "pinned",
) -> tuple[CX01ContractivityReport, CX01ContractivityReport]:
    tolerances = cx01_v0_tolerances(tolerance_profile)
    x0, y0 = _initial_pair(state_dim=int(state_dim))

    pos_distance_in, pos_distance_out, pos_empirical = _contractivity_metrics(
        x0=x0,
        y0=y0,
        contraction_factor_per_step=float(k_contract),
        steps=int(steps),
    )
    positive = CX01ContractivityCase(
        case_id="POSITIVE",
        kind="positive_control",
        update_mode="linear_scale_contractive",
        contraction_factor_per_step=float(k_contract),
        steps=int(steps),
        distance_in=float(pos_distance_in),
        distance_out=float(pos_distance_out),
        empirical_lipschitz=float(pos_empirical),
    )

    neg_distance_in, neg_distance_out, neg_empirical = _contractivity_metrics(
        x0=x0,
        y0=y0,
        contraction_factor_per_step=float(k_break),
        steps=int(steps),
    )
    negative = CX01ContractivityCase(
        case_id="NEGATIVE",
        kind="negative_control",
        update_mode="linear_scale_break",
        contraction_factor_per_step=float(k_break),
        steps=int(steps),
        distance_in=float(neg_distance_in),
        distance_out=float(neg_distance_out),
        empirical_lipschitz=float(neg_empirical),
    )

    params = {
        "state_dim": float(state_dim),
        "steps": float(steps),
        "k_contract": float(k_contract),
        "k_break": float(k_break),
        "eps_contractivity": float(tolerances["eps_contractivity"]),
        "eps_break": float(tolerances["eps_break"]),
    }

    report = CX01ContractivityReport(
        schema="CX-01/update_contractivity_front_door_report/v1",
        config_tag="cx01_update_contractivity_v0",
        regime_tag="CX01_Update_Contractivity",
        domain_tag="cx01_update_contractivity_domain_01",
        params=params,
        norm_name="l2",
        cases=[positive, negative],
    )

    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_cx01_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "cx01_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "cx01_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
