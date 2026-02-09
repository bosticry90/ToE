"""CLI for OV-OBS-01 observability metadata invariance (diagnostic-only).

Usage
  .\py.ps1 -m formal.python.tools.ovobs01_metadata_invariance --report
  .\py.ps1 -m formal.python.tools.ovobs01_metadata_invariance --write
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

from formal.python.toe.observables.ovobs01_observability_metadata_invariance import (
    ovobs01_metadata_invariance_audit,
    write_ovobs01_metadata_invariance_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--report", action="store_true", help="Print the JSON payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.report:
        # Report via the same defaults as the writer.
        out = write_ovobs01_metadata_invariance_artifact()
        payload = json.loads(out.read_text(encoding="utf-8"))
        print(json.dumps(payload, indent=2, sort_keys=True))

    if args.write:
        out = write_ovobs01_metadata_invariance_artifact()
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
