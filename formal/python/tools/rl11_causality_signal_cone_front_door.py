from __future__ import annotations

"""RL11 causality/signal-cone front door artifact writer (v0)."""

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

from formal.python.toe.comparators.rl11_causality_signal_cone_v0 import (
    RL11CausalityCase,
    RL11CausalityReport,
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
    return repo_root / "formal" / "external_evidence" / "rl11_causality_signal_cone_domain_01"


def _cone_mask(x: np.ndarray, *, x0: float, radius: float) -> np.ndarray:
    return np.abs(x - float(x0)) <= float(radius)


def _make_case(
    *,
    x: np.ndarray,
    x0: float,
    dt: float,
    steps: int,
    dx: float,
    c0: float,
    cfl_max: float,
    leakage_mass: float,
    case_id: str,
    kind: str,
) -> RL11CausalityCase:
    t_end = float(steps) * float(dt)
    radius = float(c0) * float(t_end)
    mask = _cone_mask(x, x0=x0, radius=radius)
    radius_cells = int(np.sum(mask))

    sigma = float(dx) * 2.0
    base = np.exp(-0.5 * ((x - float(x0)) / sigma) ** 2)
    psi = base * mask

    if float(leakage_mass) > 0.0:
        outside = ~mask
        count_outside = int(np.sum(outside))
        if count_outside <= 0:
            raise ValueError("No outside-of-cone region available to inject leakage.")
        leak_value = float(np.sqrt(float(leakage_mass) / float(count_outside)))
        psi = psi + leak_value * outside.astype(float)

    leakage_outside_cone = float(np.sum((psi[~mask]) ** 2))
    cfl = float(c0) * float(dt) / float(dx)

    return RL11CausalityCase(
        case_id=case_id,
        kind=kind,
        dt=float(dt),
        t_end=float(t_end),
        cfl=float(cfl),
        radius=float(radius),
        radius_cells=int(radius_cells),
        leakage_outside_cone=float(leakage_outside_cone),
        psi=[float(v) for v in psi],
    )


def generate_rl11_report(
    *,
    length: float,
    nx: int,
    dt_pos: float,
    dt_neg: float,
    steps: int,
    c0: float,
    cfl_max: float,
    eps_causal: float,
    eps_acausal: float,
    regime_tag: str,
    config_tag: str,
    domain_tag: str,
) -> RL11CausalityReport:
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)
    dx = float(length) / float(nx)
    x0 = 0.5 * float(length)

    positive = _make_case(
        x=x,
        x0=x0,
        dt=dt_pos,
        steps=steps,
        dx=dx,
        c0=c0,
        cfl_max=cfl_max,
        leakage_mass=0.0,
        case_id="POSITIVE",
        kind="positive_control",
    )

    negative = _make_case(
        x=x,
        x0=x0,
        dt=dt_neg,
        steps=steps,
        dx=dx,
        c0=c0,
        cfl_max=cfl_max,
        leakage_mass=5e-3,
        case_id="NEGATIVE",
        kind="negative_control",
    )

    return RL11CausalityReport(
        schema="RL/causality_signal_cone_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        domain_tag=domain_tag,
        params={
            "length": float(length),
            "nx": float(nx),
            "dx": float(dx),
            "c0": float(c0),
            "cfl_max": float(cfl_max),
            "dt_pos": float(dt_pos),
            "dt_neg": float(dt_neg),
            "steps": float(steps),
            "eps_causal": float(eps_causal),
            "eps_acausal": float(eps_acausal),
        },
        boundary="periodic",
        x=[float(v) for v in x],
        x0=float(x0),
        cases=[positive, negative],
    )


def write_rl11_reports(
    *,
    out_dir: Path,
    length: float,
    nx: int,
    dt_pos: float,
    dt_neg: float,
    steps: int,
    c0: float,
    cfl_max: float,
    eps_causal: float,
    eps_acausal: float,
    regime_tag: str,
    domain_tag: str,
) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    ref = generate_rl11_report(
        length=length,
        nx=nx,
        dt_pos=dt_pos,
        dt_neg=dt_neg,
        steps=steps,
        c0=c0,
        cfl_max=cfl_max,
        eps_causal=eps_causal,
        eps_acausal=eps_acausal,
        regime_tag=regime_tag,
        config_tag="rl11-ref-pinned",
        domain_tag=domain_tag,
    )
    cand = generate_rl11_report(
        length=length,
        nx=nx,
        dt_pos=dt_pos,
        dt_neg=dt_neg,
        steps=steps,
        c0=c0,
        cfl_max=cfl_max,
        eps_causal=eps_causal,
        eps_acausal=eps_acausal,
        regime_tag=regime_tag,
        config_tag="rl11-cand-pinned",
        domain_tag=domain_tag,
    )

    ref_path = out_dir / "rl11_reference_report.json"
    cand_path = out_dir / "rl11_candidate_report.json"

    ref_path.write_text(json_dumps(ref.to_jsonable()) + "\n", encoding="utf-8")
    cand_path.write_text(json_dumps(cand.to_jsonable()) + "\n", encoding="utf-8")

    return ref_path, cand_path


def json_dumps(payload: object) -> str:
    import json

    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Write RL11 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL11 artifacts.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi).")
    parser.add_argument("--nx", type=int, default=256, help="Pinned grid size.")
    parser.add_argument("--dt-pos", type=float, default=0.01, help="Pinned positive-control timestep.")
    parser.add_argument("--dt-neg", type=float, default=0.05, help="Pinned negative-control timestep.")
    parser.add_argument("--steps", type=int, default=10, help="Pinned step count for cone evaluation.")
    parser.add_argument("--c0", type=float, default=1.0, help="Pinned reference speed.")
    parser.add_argument("--cfl-max", type=float, default=1.0, help="Pinned CFL max.")
    parser.add_argument("--eps-causal", type=float, default=1e-10, help="Pinned causal leakage tolerance.")
    parser.add_argument("--eps-acausal", type=float, default=1e-3, help="Pinned acausal leakage threshold.")
    parser.add_argument("--regime-tag", type=str, default="rl11-causality-signal-cone", help="Pinned regime tag.")
    parser.add_argument("--domain-tag", type=str, default="rl11-causality-signal-cone-domain-01", help="Pinned domain tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl11_reports(
        out_dir=out_dir,
        length=args.length,
        nx=args.nx,
        dt_pos=args.dt_pos,
        dt_neg=args.dt_neg,
        steps=args.steps,
        c0=args.c0,
        cfl_max=args.cfl_max,
        eps_causal=args.eps_causal,
        eps_acausal=args.eps_acausal,
        regime_tag=args.regime_tag,
        domain_tag=args.domain_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
