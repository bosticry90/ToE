"""CLI wrapper for OV-SEL-01 selection status narrative lock.

This tool:
- Computes OV-SEL-01 (bookkeeping narrative; computed from existing locks).
- Optionally writes/updates the canonical markdown lock.
- Prints a deterministic --report summary suitable for audit logs.

Usage
  python -m formal.python.tools.ovsel01_selection_status_record --report

By default it writes the lock at:
  formal/markdown/locks/observables/OV-SEL-01_selection_status.md

Add --no-write to compute/report without touching the lock.
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
from pathlib import Path

from formal.python.toe.observables.ovsel01_selection_status_record import (
    ovsel01_selection_status_record,
    write_ovsel01_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument(
        "--lock-path",
        default=None,
        help="Override lock output path (default: canonical lock in formal/markdown/locks/observables)",
    )
    p.add_argument(
        "--status-date",
        default="2026-01-23",
        help="Status date string to embed in the record (default: 2026-01-23)",
    )

    args = p.parse_args(argv)

    rec = ovsel01_selection_status_record(status_date=str(args.status_date))

    if not args.no_write:
        lock_path = Path(args.lock_path) if args.lock_path is not None else None
        out = write_ovsel01_lock(lock_path=lock_path, status_date=str(args.status_date))
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-SEL-01 report")
        print(f"  schema: {rec.schema}")
        print(f"  status_date: {rec.status_date}")
        print(f"  OV-04x selection_status: {rec.ov04x.get('selection_status')}")
        print(f"  OV-03x selection_status: {rec.ov03x.get('selection_status')}")
        print(f"  OV-XD-04 decisiveness: {rec.ovxd04_overlap_only_comparison.get('decisiveness')}")
        print(f"  OV-XD-04 agreement: {bool(rec.ovxd04_overlap_only_comparison.get('agreement'))}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        if args.report:
            print("  narrative:")
            print(rec.narrative)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
