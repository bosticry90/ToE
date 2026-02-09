"""CLI for OV-UCFF-01 UCFF jitter-structure audit scaffold.

Usage
  .\py.ps1 -m formal.python.tools.ovucff01_jitter_structure_audit --report
  .\py.ps1 -m formal.python.tools.ovucff01_jitter_structure_audit --write

Tuning (optional)
  --seed 12345 --n-jitters 64 --jitter-frac 0.02 --k-max 6 --n-k 241
"""

from __future__ import annotations

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import json

from formal.python.toe.observables.ovucff01_jitter_structure_audit import (
    ovucff01_jitter_structure_audit,
    write_ovucff01_jitter_structure_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--seed", type=int, default=12345)
    p.add_argument("--n-jitters", type=int, default=64)
    p.add_argument("--jitter-frac", type=float, default=0.02)
    p.add_argument("--k-max", type=float, default=6.0)
    p.add_argument("--n-k", type=int, default=241)
    p.add_argument("--report", action="store_true", help="Print the JSON report")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.report:
        rep = ovucff01_jitter_structure_audit(
            seed=int(args.seed),
            n_jitters=int(args.n_jitters),
            jitter_frac=float(args.jitter_frac),
            k_max=float(args.k_max),
            n_k=int(args.n_k),
        )
        print(json.dumps(rep.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovucff01_jitter_structure_artifact(
            seed=int(args.seed),
            n_jitters=int(args.n_jitters),
            jitter_frac=float(args.jitter_frac),
            k_max=float(args.k_max),
            n_k=int(args.n_k),
        )
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
