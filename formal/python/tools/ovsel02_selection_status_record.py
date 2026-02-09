"""CLI for OV-SEL-02 selection-status comparison lock."""

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

from formal.python.toe.observables.ovsel02_selection_status_record import write_ovsel02_lock


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--write-lock", action="store_true", help="Write/update the markdown lock")
    p.add_argument("--lock-path", default=None, help="Override lock output path")
    args = p.parse_args(argv)

    if args.write_lock:
        out = write_ovsel02_lock(lock_path=Path(args.lock_path) if args.lock_path is not None else None)
        print(f"Wrote lock: {out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
