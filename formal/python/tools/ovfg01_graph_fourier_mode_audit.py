"""CLI for OV-FG-01 graph/Fourier mode audit (diagnostic-only).

Usage
  .\py.ps1 -m formal.python.tools.ovfg01_graph_fourier_mode_audit --report --n 32 --dx 0.5 --mode-m 3
  .\py.ps1 -m formal.python.tools.ovfg01_graph_fourier_mode_audit --write
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

from formal.python.toe.observables.ovfg01_graph_fourier_mode_audit import (
    ovfg01_graph_fourier_mode_audit,
    write_ovfg01_graph_fourier_mode_audit_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--n", type=int, default=32)
    p.add_argument("--dx", type=float, default=0.5)
    p.add_argument("--mode-m", type=int, default=3)
    p.add_argument("--report", action="store_true", help="Print the JSON payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.report:
        rec = ovfg01_graph_fourier_mode_audit(n=args.n, dx=args.dx, mode_m=args.mode_m)
        print(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovfg01_graph_fourier_mode_audit_artifact(n=args.n, dx=args.dx, mode_m=args.mode_m)
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
