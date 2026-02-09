"""CLI wrapper for OV-BM-01 benchmark lock (symbolic-only)."""

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
from pathlib import Path

from formal.python.toe.observables.ovbm01_mean_field_line_shift_scaling_benchmark import (
    ovbm01_mean_field_line_shift_scaling_benchmark,
    write_ovbm01_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument("--lock-path", default=None, help="Override lock output path")

    args = p.parse_args(argv)

    rec = ovbm01_mean_field_line_shift_scaling_benchmark()

    if not args.no_write:
        out = write_ovbm01_lock(lock_path=Path(args.lock_path) if args.lock_path is not None else None)
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-BM-01 report")
        print(f"  schema: {rec.schema}")
        print(f"  observable_id: {rec.observable_id}")
        print(f"  category: {rec.category}  status: {rec.status}  validation: {rec.validation}")
        print(f"  symbolic_relation_latex: {rec.symbolic_relation_latex}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
