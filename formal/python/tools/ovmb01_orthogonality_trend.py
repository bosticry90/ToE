"""CLI for OV-MB-01 orthogonality trend audit (diagnostic-only).

Usage
  .\py.ps1 -m formal.python.tools.ovmb01_orthogonality_trend --report
  .\py.ps1 -m formal.python.tools.ovmb01_orthogonality_trend --write
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

from formal.python.toe.observables.ovmb01_orthogonality_catastrophe_audit import (
    ovmb01_orthogonality_trend_audit,
    write_ovmb01_orthogonality_trend_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--filling", type=float, default=0.25)
    p.add_argument("--t", type=float, default=1.0)
    p.add_argument("--V", type=float, default=1.0)
    p.add_argument("--L", type=str, default="8,12,16,20,24,28,32", help="Comma-separated L values")
    p.add_argument("--report", action="store_true", help="Print the JSON payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    L_values = tuple(int(x.strip()) for x in str(args.L).split(",") if x.strip())

    if args.report:
        rec = ovmb01_orthogonality_trend_audit(L_values=L_values, filling=args.filling, t=args.t, V=args.V)
        print(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovmb01_orthogonality_trend_artifact(L_values=L_values, filling=args.filling, t=args.t, V=args.V)
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
