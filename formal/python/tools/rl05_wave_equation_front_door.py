from __future__ import annotations

"""RL05 wave equation front door artifact writer (v0).

Writes pinned reference/candidate artifacts for the RL05 comparator lane.
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

import numpy as np

from formal.python.toe.comparators.rl05_wave_equation_v0 import RL05WaveEquationReport


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
    return repo_root / "formal" / "external_evidence" / "rl05_wave_equation_domain_01"


def _make_report(
    *,
    t: np.ndarray,
    x: np.ndarray,
    u: np.ndarray,
    length: float,
    dt: float,
    nx: int,
    nt: int,
    c: float,
    k: float,
    amplitude: float,
    config_tag: str,
    regime_tag: str,
) -> RL05WaveEquationReport:
    return RL05WaveEquationReport(
        schema="RL/wave_equation_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={
            "length": float(length),
            "nx": float(nx),
            "dt": float(dt),
            "nt": float(nt),
            "c": float(c),
            "k": float(k),
            "amplitude": float(amplitude),
        },
        boundary="periodic",
        t=[float(v) for v in t],
        x=[float(v) for v in x],
        u=[[float(v) for v in row] for row in u],
    )


def write_rl05_reports(*, out_dir: Path, nx: int, nt: int, length: float, dt: float, c: float, k: float, amplitude: float, regime_tag: str) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    t = np.linspace(0.0, float(dt) * float(nt - 1), int(nt))

    u = amplitude * np.sin(k * (x[None, :] - c * t[:, None]))

    ref = _make_report(
        t=t,
        x=x,
        u=u,
        length=length,
        dt=dt,
        nx=nx,
        nt=nt,
        c=c,
        k=k,
        amplitude=amplitude,
        config_tag="rl05-ref-pinned",
        regime_tag=regime_tag,
    )
    cand = _make_report(
        t=t,
        x=x,
        u=u,
        length=length,
        dt=dt,
        nx=nx,
        nt=nt,
        c=c,
        k=k,
        amplitude=amplitude,
        config_tag="rl05-cand-pinned",
        regime_tag=regime_tag,
    )

    ref_path = out_dir / "rl05_reference_report.json"
    cand_path = out_dir / "rl05_candidate_report.json"

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
    parser = argparse.ArgumentParser(description="Write RL05 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL05 artifacts.")
    parser.add_argument("--nx", type=int, default=128, help="Pinned grid size.")
    parser.add_argument("--nt", type=int, default=32, help="Pinned time steps.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi by default).")
    parser.add_argument("--dt", type=float, default=0.1, help="Pinned time step.")
    parser.add_argument("--c", type=float, default=1.0, help="Pinned wave speed.")
    parser.add_argument("--k", type=float, default=1.0, help="Pinned wave number.")
    parser.add_argument("--amplitude", type=float, default=1.0, help="Pinned amplitude.")
    parser.add_argument("--regime-tag", type=str, default="rl05-wave", help="Pinned regime tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl05_reports(
        out_dir=out_dir,
        nx=args.nx,
        nt=args.nt,
        length=args.length,
        dt=args.dt,
        c=args.c,
        k=args.k,
        amplitude=args.amplitude,
        regime_tag=args.regime_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
