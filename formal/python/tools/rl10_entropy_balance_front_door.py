from __future__ import annotations

"""RL10 entropy balance front door artifact writer (v0)."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.rl10_entropy_balance_v0 import (
    RL10EntropyCase,
    RL10EntropyReport,
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
    return repo_root / "formal" / "external_evidence" / "rl10_entropy_balance_domain_01"


def _stationary_distribution(transition: np.ndarray) -> np.ndarray:
    eigvals, eigvecs = np.linalg.eig(transition.T)
    idx = int(np.argmin(np.abs(eigvals - 1.0)))
    vec = np.real(eigvecs[:, idx])
    if np.all(vec <= 0):
        vec = -vec
    vec = np.abs(vec)
    vec_sum = float(np.sum(vec))
    if vec_sum <= 0:
        raise ValueError("Stationary distribution computation failed.")
    return vec / vec_sum


def _entropy_production(transition: np.ndarray, pi: np.ndarray) -> float:
    p = transition
    pi_col = pi[:, None]
    flow = pi_col * p
    flow_t = flow.T
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(flow_t > 0, flow / flow_t, 1.0)
        log_ratio = np.log(ratio)
    sigma = float(np.sum(flow * log_ratio))
    return sigma


def _detailed_balance_residual(transition: np.ndarray, pi: np.ndarray) -> float:
    p = transition
    pi_col = pi[:, None]
    resid = pi_col * p - (pi_col * p).T
    return float(np.max(np.abs(resid)))


def _case_metrics(matrix: np.ndarray) -> tuple[np.ndarray, float, float]:
    pi = _stationary_distribution(matrix)
    sigma = _entropy_production(matrix, pi)
    db_residual = _detailed_balance_residual(matrix, pi)
    return pi, sigma, db_residual


def generate_rl10_report(
    *,
    eps_balance: float,
    eps_entropy: float,
    regime_tag: str,
    config_tag: str,
    domain_tag: str,
) -> RL10EntropyReport:
    p_pos = np.array(
        [
            [0.7, 0.2, 0.1],
            [0.2, 0.6, 0.2],
            [0.1, 0.2, 0.7],
        ],
        dtype=float,
    )
    p_neg = np.array(
        [
            [0.7, 0.25, 0.05],
            [0.05, 0.7, 0.25],
            [0.25, 0.05, 0.7],
        ],
        dtype=float,
    )

    pi, sigma, db_residual = _case_metrics(p_pos)
    positive = RL10EntropyCase(
        case_id="POSITIVE",
        kind="positive_control",
        transition_matrix=[[float(v) for v in row] for row in p_pos],
        stationary_pi=[float(v) for v in pi],
        sigma_proxy=float(sigma),
        db_residual=float(db_residual),
    )

    pi, sigma, db_residual = _case_metrics(p_neg)
    negative = RL10EntropyCase(
        case_id="NEGATIVE",
        kind="negative_control",
        transition_matrix=[[float(v) for v in row] for row in p_neg],
        stationary_pi=[float(v) for v in pi],
        sigma_proxy=float(sigma),
        db_residual=float(db_residual),
    )

    return RL10EntropyReport(
        schema="RL/entropy_balance_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        domain_tag=domain_tag,
        params={
            "state_count": 3.0,
            "eps_balance": float(eps_balance),
            "eps_entropy": float(eps_entropy),
        },
        boundary="markov_chain",
        cases=[positive, negative],
    )


def write_rl10_reports(
    *,
    out_dir: Path,
    eps_balance: float,
    eps_entropy: float,
    regime_tag: str,
    domain_tag: str,
) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    ref = generate_rl10_report(
        eps_balance=eps_balance,
        eps_entropy=eps_entropy,
        regime_tag=regime_tag,
        config_tag="rl10-ref-pinned",
        domain_tag=domain_tag,
    )
    cand = generate_rl10_report(
        eps_balance=eps_balance,
        eps_entropy=eps_entropy,
        regime_tag=regime_tag,
        config_tag="rl10-cand-pinned",
        domain_tag=domain_tag,
    )

    ref_path = out_dir / "rl10_reference_report.json"
    cand_path = out_dir / "rl10_candidate_report.json"

    ref_path.write_text(json_dumps(ref.to_jsonable()) + "\n", encoding="utf-8")
    cand_path.write_text(json_dumps(cand.to_jsonable()) + "\n", encoding="utf-8")

    return ref_path, cand_path


def json_dumps(payload: object) -> str:
    import json

    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Write RL10 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL10 artifacts.")
    parser.add_argument("--eps-balance", type=float, default=1e-8, help="Pinned balance tolerance.")
    parser.add_argument("--eps-entropy", type=float, default=1e-3, help="Pinned entropy tolerance.")
    parser.add_argument("--regime-tag", type=str, default="rl10-entropy-balance", help="Pinned regime tag.")
    parser.add_argument("--domain-tag", type=str, default="rl10-entropy-balance-domain-01", help="Pinned domain tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl10_reports(
        out_dir=out_dir,
        eps_balance=args.eps_balance,
        eps_entropy=args.eps_entropy,
        regime_tag=args.regime_tag,
        domain_tag=args.domain_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
