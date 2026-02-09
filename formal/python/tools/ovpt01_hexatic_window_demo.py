"""CLI for OV-PT-01 hexatic window detector demo artifact.

Usage
  .\py.ps1 -m formal.python.tools.ovpt01_hexatic_window_demo --write
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

from formal.python.toe.observables.ovpt01_phase_transition_window_audit import (
    write_ovpt01_hexatic_window_demo_artifact,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--write", action="store_true", help="Write the canonical demo JSON artifact")
    args = p.parse_args(argv)

    if args.write:
        out = write_ovpt01_hexatic_window_demo_artifact()
        print(f"Wrote {out.as_posix()}")
        return 0

    p.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
