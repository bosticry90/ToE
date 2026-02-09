from __future__ import annotations

"""RL01 relativistic dispersion front door artifact writer (v0).

Writes pinned reference/candidate artifacts for the RL01 comparator lane.
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

from formal.python.toe.comparators.rl01_relativistic_dispersion_v0 import (
    RL01DispersionReport,
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
    return repo_root / "formal" / "external_evidence" / "relativistic_dispersion_domain_01"


def _make_report(*, k: Iterable[float], c: float, m: float, config_tag: str, regime_tag: str) -> RL01DispersionReport:
    k_list = [float(x) for x in k]
    omega2 = [(c * c) * (kk * kk) + (m * m) for kk in k_list]
    return RL01DispersionReport(
        schema="RL/dispersion_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"c": float(c), "m": float(m)},
        k=k_list,
        omega2=omega2,
    )


def write_rl01_reports(*, out_dir: Path, c: float, m: float, regime_tag: str) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k, c=c, m=m, config_tag="rl01-ref-pinned", regime_tag=regime_tag)
    cand = _make_report(k=k, c=c, m=m, config_tag="rl01-cand-pinned", regime_tag=regime_tag)

    ref_path = out_dir / "rl01_reference_report.json"
    cand_path = out_dir / "rl01_candidate_report.json"

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
    parser = argparse.ArgumentParser(description="Write RL01 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL01 artifacts.")
    parser.add_argument("--c", type=float, default=1.0, help="Pinned c parameter.")
    parser.add_argument("--m", type=float, default=1.0, help="Pinned m parameter.")
    parser.add_argument("--regime-tag", type=str, default="rl01-lowk", help="Pinned regime tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl01_reports(out_dir=out_dir, c=args.c, m=args.m, regime_tag=args.regime_tag)
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
