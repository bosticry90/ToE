from __future__ import annotations

"""RL08 gauge redundancy invariance front door artifact writer (v0)."""

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

from formal.python.toe.comparators.rl08_gauge_redundancy_invariance_v0 import (
    RL08GaugeCase,
    RL08GaugeReport,
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
    return repo_root / "formal" / "external_evidence" / "rl08_gauge_redundancy_invariance_domain_01"


def _complex_field(x: np.ndarray) -> np.ndarray:
    real = 1.0 + 0.2 * np.cos(x) + 0.1 * np.cos(2.0 * x)
    imag = 0.3 * np.sin(x) + 0.1 * np.sin(2.0 * x)
    return real + 1j * imag


def generate_rl08_report(
    *,
    nx: int,
    length: float,
    alpha: float,
    eps_invariant: float,
    eps_break: float,
    regime_tag: str,
    config_tag: str,
    domain_tag: str,
) -> RL08GaugeReport:
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    dx = float(length) / float(nx)
    psi = _complex_field(x)

    phi = float(alpha) * np.sin(2.0 * np.pi * x / float(length))
    gauge = np.exp(1j * phi)
    psi_g = psi * gauge

    rho = np.abs(psi) ** 2
    rho_g = np.abs(psi_g) ** 2
    residual_invariant = float(np.max(np.abs(rho - rho_g)))

    obs_bad = psi.real
    obs_bad_g = psi_g.real
    residual_break = float(np.max(np.abs(obs_bad - obs_bad_g)))

    cases = [
        RL08GaugeCase(
            case_id="POSITIVE",
            kind="positive_control",
            residual_maxabs=residual_invariant,
        ),
        RL08GaugeCase(
            case_id="NEGATIVE",
            kind="negative_control",
            residual_maxabs=residual_break,
        ),
    ]

    return RL08GaugeReport(
        schema="RL/gauge_redundancy_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        domain_tag=domain_tag,
        params={
            "length": float(length),
            "nx": float(nx),
            "dx": float(dx),
            "alpha": float(alpha),
            "eps_invariant": float(eps_invariant),
            "eps_break": float(eps_break),
        },
        boundary="periodic",
        x=[float(v) for v in x],
        psi_real=[float(v) for v in psi.real],
        psi_imag=[float(v) for v in psi.imag],
        phi=[float(v) for v in phi],
        rho=[float(v) for v in rho],
        rho_gauge=[float(v) for v in rho_g],
        obs_bad=[float(v) for v in obs_bad],
        obs_bad_gauge=[float(v) for v in obs_bad_g],
        cases=cases,
    )


def write_rl08_reports(
    *,
    out_dir: Path,
    nx: int,
    length: float,
    alpha: float,
    eps_invariant: float,
    eps_break: float,
    regime_tag: str,
    domain_tag: str,
) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    ref = generate_rl08_report(
        nx=nx,
        length=length,
        alpha=alpha,
        eps_invariant=eps_invariant,
        eps_break=eps_break,
        regime_tag=regime_tag,
        config_tag="rl08-ref-pinned",
        domain_tag=domain_tag,
    )
    cand = generate_rl08_report(
        nx=nx,
        length=length,
        alpha=alpha,
        eps_invariant=eps_invariant,
        eps_break=eps_break,
        regime_tag=regime_tag,
        config_tag="rl08-cand-pinned",
        domain_tag=domain_tag,
    )

    ref_path = out_dir / "rl08_reference_report.json"
    cand_path = out_dir / "rl08_candidate_report.json"

    ref_path.write_text(json_dumps(ref.to_jsonable()) + "\n", encoding="utf-8")
    cand_path.write_text(json_dumps(cand.to_jsonable()) + "\n", encoding="utf-8")

    return ref_path, cand_path


def json_dumps(payload: object) -> str:
    import json

    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Write RL08 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL08 artifacts.")
    parser.add_argument("--nx", type=int, default=128, help="Pinned grid size.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi).")
    parser.add_argument("--alpha", type=float, default=0.2, help="Pinned gauge amplitude.")
    parser.add_argument("--eps-invariant", type=float, default=1e-10, help="Pinned invariance tolerance.")
    parser.add_argument("--eps-break", type=float, default=1e-3, help="Pinned break tolerance.")
    parser.add_argument("--regime-tag", type=str, default="rl08-gauge-redundancy", help="Pinned regime tag.")
    parser.add_argument("--domain-tag", type=str, default="rl08-gauge-redundancy-domain-01", help="Pinned domain tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl08_reports(
        out_dir=out_dir,
        nx=args.nx,
        length=args.length,
        alpha=args.alpha,
        eps_invariant=args.eps_invariant,
        eps_break=args.eps_break,
        regime_tag=args.regime_tag,
        domain_tag=args.domain_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
