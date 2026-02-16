from __future__ import annotations

"""RL06 phase winding quantization front door artifact writer (v0).

Writes pinned reference/candidate artifacts for the RL06 comparator lane.
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

from formal.python.toe.comparators.rl06_phase_winding_quantization_v0 import (
    RL06PhaseWindingReport,
    RL06WindingCase,
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
    return repo_root / "formal" / "external_evidence" / "rl06_phase_winding_quantization_domain_01"


def _make_case(*, x: np.ndarray, length: float, k: float, amplitude: float, case_id: str, kind: str) -> RL06WindingCase:
    theta = 2.0 * np.pi * float(k) * x / float(length)
    psi = float(amplitude) * np.exp(1j * theta)
    return RL06WindingCase(
        case_id=case_id,
        kind=kind,
        k_target=int(round(float(k))),
        psi_real=[float(v) for v in psi.real],
        psi_imag=[float(v) for v in psi.imag],
    )


def write_rl06_reports(*, out_dir: Path, nx: int, length: float, k_target: int, alpha_nonint: float, amplitude: float, regime_tag: str) -> tuple[Path, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    x = np.linspace(0.0, float(length), int(nx), endpoint=False)

    quantized = _make_case(
        x=x,
        length=length,
        k=float(k_target),
        amplitude=amplitude,
        case_id="QUANTIZED",
        kind="quantized",
    )
    nonint_case = _make_case(
        x=x,
        length=length,
        k=float(k_target) + float(alpha_nonint),
        amplitude=amplitude,
        case_id="NONINT",
        kind="negative_control",
    )

    ref = RL06PhaseWindingReport(
        schema="RL/phase_winding_front_door_report/v1",
        config_tag="rl06-ref-pinned",
        regime_tag=regime_tag,
        params={
            "length": float(length),
            "nx": float(nx),
            "k_target": float(k_target),
            "alpha_nonint": float(alpha_nonint),
            "amplitude": float(amplitude),
        },
        boundary="periodic",
        unwrap_method="cumulative_principal_value",
        x=[float(v) for v in x],
        cases=[quantized, nonint_case],
    )
    cand = RL06PhaseWindingReport(
        schema="RL/phase_winding_front_door_report/v1",
        config_tag="rl06-cand-pinned",
        regime_tag=regime_tag,
        params={
            "length": float(length),
            "nx": float(nx),
            "k_target": float(k_target),
            "alpha_nonint": float(alpha_nonint),
            "amplitude": float(amplitude),
        },
        boundary="periodic",
        unwrap_method="cumulative_principal_value",
        x=[float(v) for v in x],
        cases=[quantized, nonint_case],
    )

    ref_path = out_dir / "rl06_reference_report.json"
    cand_path = out_dir / "rl06_candidate_report.json"

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
    parser = argparse.ArgumentParser(description="Write RL06 pinned front door artifacts.")
    parser.add_argument("--out-dir", type=Path, default=None, help="Output directory for RL06 artifacts.")
    parser.add_argument("--nx", type=int, default=128, help="Pinned grid size.")
    parser.add_argument("--length", type=float, default=6.283185307179586, help="Pinned domain length (2*pi by default).")
    parser.add_argument("--k-target", type=int, default=2, help="Pinned integer winding target.")
    parser.add_argument("--alpha-nonint", type=float, default=0.35, help="Pinned non-integer winding offset for negative control.")
    parser.add_argument("--amplitude", type=float, default=1.0, help="Pinned amplitude.")
    parser.add_argument("--regime-tag", type=str, default="rl06-phase-winding", help="Pinned regime tag.")
    args = parser.parse_args()

    repo_root = _find_repo_root(Path(__file__))
    out_dir = args.out_dir or _default_artifact_dir(repo_root)

    ref_path, cand_path = write_rl06_reports(
        out_dir=out_dir,
        nx=args.nx,
        length=args.length,
        k_target=args.k_target,
        alpha_nonint=args.alpha_nonint,
        amplitude=args.amplitude,
        regime_tag=args.regime_tag,
    )
    print(f"Wrote {ref_path}")
    print(f"Wrote {cand_path}")


if __name__ == "__main__":
    main()
