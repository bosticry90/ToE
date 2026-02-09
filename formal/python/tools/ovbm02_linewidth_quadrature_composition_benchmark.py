"""CLI wrapper for OV-BM-02 benchmark lock (symbolic-only)."""

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

from formal.python.toe.observables.ovbm02_linewidth_quadrature_composition_benchmark import (
    ovbm02_linewidth_quadrature_composition_benchmark,
    write_ovbm02_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument("--lock-path", default=None, help="Override lock output path")

    args = p.parse_args(argv)

    rec = ovbm02_linewidth_quadrature_composition_benchmark()

    if not args.no_write:
        out = write_ovbm02_lock(lock_path=Path(args.lock_path) if args.lock_path is not None else None)
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-BM-02 report")
        print(f"  schema: {rec.schema}")
        print(f"  observable_id: {rec.observable_id}")
        print(f"  category: {rec.category}  status: {rec.status}  validation: {rec.validation}")
        print(f"  symbolic_relation_latex: {rec.symbolic_relation_latex}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
