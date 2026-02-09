from __future__ import annotations

"""RL02 nonrelativistic NLSE front door artifact writer (v0).

Writes pinned reference/candidate artifacts for the RL02 comparator lane.
"""

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
from typing import Iterable

from formal.python.toe.comparators.rl02_nonrelativistic_nlse_v0 import RL02NLSEReport


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
    return repo_root / "formal" / "external_evidence" / "rl02_nonrelativistic_limit_nlse_domain_01"


def _make_report(
    *,
    k: Iterable[float],
    m: float,
    mu: float,
    epsilon: float,
    config_tag: str,
    regime_tag: str,
) -> RL02NLSEReport:
    k_list = [float(x) for x in k]
    omega = [(kk * kk) / (2.0 * float(m)) + float(mu) for kk in k_list]
    return RL02NLSEReport(
        schema="RL/nr_nlse_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"m": float(m), "mu": float(mu), "epsilon": float(epsilon)},
        k=k_list,
        omega=omega,
    )


def write_rl02_reports(*, out_dir: Path, m: float, mu: float, epsilon: float, regime_tag: str) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k, m=m, mu=mu, epsilon=epsilon, config_tag="rl02-ref-pinned", regime_tag=regime_tag)
    cand = _make_report(k=k, m=m, mu=mu, epsilon=epsilon, config_tag="rl02-cand-pinned", regime_tag=regime_tag)

    ref_path = out_dir / "rl02_reference_report.json"
    cand_path = out_dir / "rl02_candidate_report.json"

    ref_path.write_text(
        json_dumps(ref.to_jsonable()) + "\n",
        encoding="utf-8",
    )
    cand_path.write_text(
        json_dumps(cand.to_jsonable()) + "\n",
        encoding="utf-8",
    )

    return ref_path, cand_path


def json_dumps(payload: object) -> str:
    import json

    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Write RL02 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL02 artifacts.")
    parser.add_argument("--m", type=float, default=1.0, help="Pinned mass parameter.")
    parser.add_argument("--mu", type=float, default=1.0, help="Pinned chemical potential.")
    parser.add_argument("--epsilon", type=float, default=0.01, help="Pinned nonrelativistic scaling parameter.")
    parser.add_argument("--regime-tag", type=str, default="rl02-lowk", help="Pinned regime tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl02_reports(
        out_dir=out_dir,
        m=args.m,
        mu=args.mu,
        epsilon=args.epsilon,
        regime_tag=args.regime_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
