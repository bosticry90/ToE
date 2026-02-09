"""CLI for OV-DQ-01 adequacy drilldown (window-level).

Usage
  python -m formal.python.tools.ovdq01_adequacy_drilldown_record --report
  python -m formal.python.tools.ovdq01_adequacy_drilldown_record --write
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

from formal.python.toe.observables.ovdq01_adequacy_drilldown_record import (
    ovdq01_adequacy_drilldown_record,
    write_ovdq01_adequacy_drilldown_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--adequacy-policy", default="DQ-01_v1")
    p.add_argument("--report", action="store_true", help="Print the JSON payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    rec = ovdq01_adequacy_drilldown_record(adequacy_policy=str(args.adequacy_policy))

    if args.report:
        print(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovdq01_adequacy_drilldown_artifact(adequacy_policy=str(args.adequacy_policy))
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
