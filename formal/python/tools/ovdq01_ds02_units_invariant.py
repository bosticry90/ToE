"""CLI for OV-DQ-01 DS-02 units invariant (diagnostic-only).

Usage
  python -m formal.python.tools.ovdq01_ds02_units_invariant --report
  python -m formal.python.tools.ovdq01_ds02_units_invariant --write
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

from formal.python.toe.observables.ovdq01_ds02_units_invariant import (
    ovdq01_ds02_units_invariant_record,
    write_ds02_units_invariant_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--report", action="store_true", help="Print the JSON payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    rec = ovdq01_ds02_units_invariant_record()

    if args.report:
        print(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ds02_units_invariant_artifact()
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
