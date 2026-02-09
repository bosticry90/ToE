from __future__ import annotations

"""Toy gauge-redundancy report generator (quarantine-safe).

Goal
- Emit a deterministic, pinned Family H report artifact.
- Bookkeeping only; no physics claim.

Report schema (v1)
- Delegates to the front door report: TOY/gauge_redundancy_report/v1
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
from typing import Optional

from formal.python.tools.toy_gauge_redundancy_front_door import (
    GaugeStateInput,
    ToyHInput,
    ToyHParams,
    build_toy_gauge_redundancy_report,
    dumps_toy_gauge_redundancy_report,
)

DEFAULT_OUT_PATH = "formal/output/toy_gauge_redundancy_report_H1_pinned.json"
DEFAULT_OUT_PATH_H2 = "formal/output/toy_gauge_redundancy_report_H2_pinned.json"

PINNED_INPUTS: dict[str, ToyHInput] = {
    "H1_phase_gauge": ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4]]),
        params=ToyHParams(dt=0.1, steps=3, theta=0.45, epsilon=1e-9, gauge_kind="phase_rotate"),
        candidate_id="H1_phase_gauge",
    ),
    "H2_local_phase_gauge": ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4], [0.1, -0.2]]),
        params=ToyHParams(
            dt=0.1,
            steps=3,
            theta=0.4,
            theta_step=0.21,
            epsilon=1e-9,
            gauge_kind="local_phase_rotate",
        ),
        candidate_id="H2_local_phase_gauge",
    ),
}


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def build_toy_gauge_redundancy_report_payload(*, candidate_id: str = "H1_phase_gauge") -> dict:
    if candidate_id not in PINNED_INPUTS:
        raise ValueError(f"Unsupported candidate_id: {candidate_id}")
    return build_toy_gauge_redundancy_report(PINNED_INPUTS[candidate_id])


def render_toy_gauge_redundancy_report_text(payload: dict) -> str:
    return dumps_toy_gauge_redundancy_report(payload)


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the pinned toy gauge-redundancy report (schema v1).")
    p.add_argument(
        "--candidate-id",
        choices=sorted(PINNED_INPUTS.keys()),
        default="H1_phase_gauge",
        help="Pinned candidate id to emit (default: H1_phase_gauge)",
    )
    p.add_argument(
        "--out",
        default=None,
        help="Repo-relative output JSON path (default: pinned path for the candidate)",
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    candidate_id = str(args.candidate_id)
    payload = build_toy_gauge_redundancy_report_payload(candidate_id=candidate_id)
    out_text = render_toy_gauge_redundancy_report_text(payload)

    if not args.no_write:
        if args.out:
            out_rel = str(args.out)
        else:
            out_rel = DEFAULT_OUT_PATH if candidate_id == "H1_phase_gauge" else DEFAULT_OUT_PATH_H2
        out_path = repo_root / out_rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")
        print(str(Path(out_rel).as_posix()))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
