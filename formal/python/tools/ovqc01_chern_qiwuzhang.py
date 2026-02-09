"""CLI for OV-QC-01 Chern number (Qi-Wu-Zhang) audit primitive.

Usage
  .\py.ps1 -m formal.python.tools.ovqc01_chern_qiwuzhang --report --m -1.0 --grid-n 25
  .\py.ps1 -m formal.python.tools.ovqc01_chern_qiwuzhang --write
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

from formal.python.toe.observables.ovqc01_berry_curvature_audit import (
    ovqc01_chern_number_qiwuzhang,
    write_ovqc01_chern_qiwuzhang_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m", type=float, default=-1.0)
    p.add_argument("--grid-n", type=int, default=25)
    p.add_argument("--report", action="store_true", help="Print the JSON payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.report:
        rec = ovqc01_chern_number_qiwuzhang(m=args.m, grid_n=args.grid_n)
        print(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovqc01_chern_qiwuzhang_artifact(m=args.m, grid_n=args.grid_n)
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
