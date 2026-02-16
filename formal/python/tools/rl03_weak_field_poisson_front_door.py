from __future__ import annotations

"""RL03 weak-field Poisson front door artifact writer (v0).

Writes pinned reference/candidate artifacts for the RL03 comparator lane.
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

import numpy as np

from formal.python.toe.comparators.rl03_weak_field_poisson_v0 import RL03PoissonReport


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
    return repo_root / "formal" / "external_evidence" / "rl03_weak_field_poisson_domain_01"


def _poisson_solve_periodic(*, rho: np.ndarray, kappa: float, length: float) -> np.ndarray:
    nx = int(rho.size)
    dx = float(length) / float(nx)
    k = 2.0 * np.pi * np.fft.fftfreq(nx, d=dx)
    rho_hat = np.fft.fft(rho)
    k2 = k * k

    phi_hat = np.zeros_like(rho_hat)
    mask = k2 > 0.0
    phi_hat[mask] = -(kappa * rho_hat[mask]) / k2[mask]
    phi = np.fft.ifft(phi_hat).real
    phi -= float(np.mean(phi))
    return phi


def _make_report(
    *,
    x: Iterable[float],
    rho: Iterable[float],
    phi: Iterable[float],
    kappa: float,
    length: float,
    nx: int,
    config_tag: str,
    regime_tag: str,
) -> RL03PoissonReport:
    return RL03PoissonReport(
        schema="RL/weak_field_poisson_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"kappa": float(kappa), "length": float(length), "nx": float(nx)},
        boundary="periodic",
        gauge="mean_zero",
        x=[float(v) for v in x],
        rho=[float(v) for v in rho],
        phi=[float(v) for v in phi],
    )


def write_rl03_reports(*, out_dir: Path, nx: int, length: float, kappa: float, regime_tag: str) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    sigma = float(length) / 10.0
    rho = np.exp(-0.5 * ((x - 0.5 * float(length)) / sigma) ** 2)
    phi = _poisson_solve_periodic(rho=rho, kappa=float(kappa), length=float(length))

    ref = _make_report(
        x=x,
        rho=rho,
        phi=phi,
        kappa=kappa,
        length=length,
        nx=nx,
        config_tag="rl03-ref-pinned",
        regime_tag=regime_tag,
    )
    cand = _make_report(
        x=x,
        rho=rho,
        phi=phi,
        kappa=kappa,
        length=length,
        nx=nx,
        config_tag="rl03-cand-pinned",
        regime_tag=regime_tag,
    )

    ref_path = out_dir / "rl03_reference_report.json"
    cand_path = out_dir / "rl03_candidate_report.json"

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
    parser = argparse.ArgumentParser(description="Write RL03 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL03 artifacts.")
    parser.add_argument("--nx", type=int, default=128, help="Pinned grid size.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi by default).")
    parser.add_argument("--kappa", type=float, default=1.0, help="Pinned Poisson scaling constant.")
    parser.add_argument("--regime-tag", type=str, default="rl03-weak-field", help="Pinned regime tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl03_reports(
        out_dir=out_dir,
        nx=args.nx,
        length=args.length,
        kappa=args.kappa,
        regime_tag=args.regime_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
