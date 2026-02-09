from __future__ import annotations

"""Toy topological-invariants report generator (quarantine-safe).

Goal
- Emit a deterministic, pinned Family G report artifact.
- Bookkeeping only; no physics claim.

Report schema (v1)
- Delegates to the front door report: TOY/topological_invariants_report/v1
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

from formal.python.tools.toy_topological_invariants_front_door import (
    TopologicalStateInput,
    ToyGInput,
    ToyGParams,
    build_toy_topological_invariants_report,
    dumps_toy_topological_invariants_report,
)

DEFAULT_OUT_PATH = "formal/output/toy_topological_invariants_report_G1_pinned.json"

PINNED_INPUT = ToyGInput(
    state=TopologicalStateInput(grid=[1.0, -1.0, 1.0, -1.0, 1.0]),
    params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
    candidate_id="G1_sign_change",
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


def build_toy_topological_invariants_report_payload() -> dict:
    return build_toy_topological_invariants_report(PINNED_INPUT)


def render_toy_topological_invariants_report_text(payload: dict) -> str:
    return dumps_toy_topological_invariants_report(payload)


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the pinned toy topological-invariants report (schema v1).")
    p.add_argument(
        "--out",
        default=DEFAULT_OUT_PATH,
        help=f"Repo-relative output JSON path (default: {DEFAULT_OUT_PATH})",
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_toy_topological_invariants_report_payload()
    out_text = render_toy_topological_invariants_report_text(payload)

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")
        print(str(Path(args.out).as_posix()))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
