from __future__ import annotations

"""RL09 dispersion-topology bridge front door artifact writer (v0)."""

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

from formal.python.toe.comparators.rl09_dispersion_topology_bridge_v0 import (
    RL09TopologyCase,
    RL09TopologyReport,
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
    return repo_root / "formal" / "external_evidence" / "rl09_dispersion_topology_bridge_domain_01"


def _compute_winding(*, k: np.ndarray, t1: float, t2: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, float, float, int, float]:
    dx = t1 + t2 * np.cos(k)
    dy = t2 * np.sin(k)
    energy = np.sqrt(dx * dx + dy * dy)
    theta_raw = np.arctan2(dy, dx)
    theta = np.unwrap(theta_raw)
    diffs = np.diff(theta_raw, append=theta_raw[0])
    diffs_wrapped = (diffs + np.pi) % (2.0 * np.pi) - np.pi
    winding_raw = float(np.sum(diffs_wrapped) / (2.0 * np.pi))
    theta_delta = float(theta[-1] - theta[0])
    winding_rounded = int(round(winding_raw))
    min_energy = float(np.min(energy))
    return dx, dy, energy, theta, theta_delta, winding_raw, winding_rounded, min_energy


def generate_rl09_report(
    *,
    length: float,
    nk: int,
    t1_pos: float,
    t2_pos: float,
    t1_neg: float,
    t2_neg: float,
    eps_winding: float,
    regime_tag: str,
    config_tag: str,
    domain_tag: str,
) -> RL09TopologyReport:
    k = np.linspace(0.0, float(length), int(nk), endpoint=False)

    dx, dy, energy, theta, theta_delta, winding_raw, winding_rounded, min_energy = _compute_winding(
        k=k,
        t1=t1_pos,
        t2=t2_pos,
    )
    abs_err = abs(winding_raw - 1.0)
    positive = RL09TopologyCase(
        case_id="POSITIVE",
        kind="positive_control",
        t1=float(t1_pos),
        t2=float(t2_pos),
        dx=[float(v) for v in dx],
        dy=[float(v) for v in dy],
        energy=[float(v) for v in energy],
        theta=[float(v) for v in theta],
        theta_delta=float(theta_delta),
        winding_raw=float(winding_raw),
        winding_rounded=int(winding_rounded),
        abs_err=float(abs_err),
        min_energy=float(min_energy),
    )

    dx, dy, energy, theta, theta_delta, winding_raw, winding_rounded, min_energy = _compute_winding(
        k=k,
        t1=t1_neg,
        t2=t2_neg,
    )
    abs_err = abs(winding_raw - 0.0)
    negative = RL09TopologyCase(
        case_id="NEGATIVE",
        kind="negative_control",
        t1=float(t1_neg),
        t2=float(t2_neg),
        dx=[float(v) for v in dx],
        dy=[float(v) for v in dy],
        energy=[float(v) for v in energy],
        theta=[float(v) for v in theta],
        theta_delta=float(theta_delta),
        winding_raw=float(winding_raw),
        winding_rounded=int(winding_rounded),
        abs_err=float(abs_err),
        min_energy=float(min_energy),
    )

    cases = [positive, negative]

    return RL09TopologyReport(
        schema="RL/dispersion_topology_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        domain_tag=domain_tag,
        params={
            "length": float(length),
            "nk": float(nk),
            "t1_pos": float(t1_pos),
            "t2_pos": float(t2_pos),
            "t1_neg": float(t1_neg),
            "t2_neg": float(t2_neg),
            "eps_winding": float(eps_winding),
        },
        boundary="periodic",
        k=[float(v) for v in k],
        cases=cases,
    )


def write_rl09_reports(
    *,
    out_dir: Path,
    length: float,
    nk: int,
    eps_winding: float,
    regime_tag: str,
    domain_tag: str,
    t1_pos: float,
    t2_pos: float,
    t1_neg: float,
    t2_neg: float,
) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    ref = generate_rl09_report(
        length=length,
        nk=nk,
        t1_pos=t1_pos,
        t2_pos=t2_pos,
        t1_neg=t1_neg,
        t2_neg=t2_neg,
        eps_winding=eps_winding,
        regime_tag=regime_tag,
        config_tag="rl09-ref-pinned",
        domain_tag=domain_tag,
    )
    cand = generate_rl09_report(
        length=length,
        nk=nk,
        t1_pos=t1_pos,
        t2_pos=t2_pos,
        t1_neg=t1_neg,
        t2_neg=t2_neg,
        eps_winding=eps_winding,
        regime_tag=regime_tag,
        config_tag="rl09-cand-pinned",
        domain_tag=domain_tag,
    )

    ref_path = out_dir / "rl09_reference_report.json"
    cand_path = out_dir / "rl09_candidate_report.json"

    ref_path.write_text(json_dumps(ref.to_jsonable()) + "\n", encoding="utf-8")
    cand_path.write_text(json_dumps(cand.to_jsonable()) + "\n", encoding="utf-8")

    return ref_path, cand_path


def json_dumps(payload: object) -> str:
    import json

    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Write RL09 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL09 artifacts.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi).")
    parser.add_argument("--nk", type=int, default=256, help="Pinned k-grid size.")
    parser.add_argument("--eps-winding", type=float, default=1e-8, help="Pinned winding tolerance.")
    parser.add_argument("--t1-pos", type=float, default=0.5, help="Pinned positive-control t1.")
    parser.add_argument("--t2-pos", type=float, default=1.0, help="Pinned positive-control t2.")
    parser.add_argument("--t1-neg", type=float, default=1.0, help="Pinned negative-control t1.")
    parser.add_argument("--t2-neg", type=float, default=0.5, help="Pinned negative-control t2.")
    parser.add_argument("--regime-tag", type=str, default="rl09-dispersion-topology", help="Pinned regime tag.")
    parser.add_argument("--domain-tag", type=str, default="rl09-dispersion-topology-domain-01", help="Pinned domain tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl09_reports(
        out_dir=out_dir,
        length=args.length,
        nk=args.nk,
        eps_winding=args.eps_winding,
        regime_tag=args.regime_tag,
        domain_tag=args.domain_tag,
        t1_pos=args.t1_pos,
        t2_pos=args.t2_pos,
        t1_neg=args.t1_neg,
        t2_neg=args.t2_neg,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
