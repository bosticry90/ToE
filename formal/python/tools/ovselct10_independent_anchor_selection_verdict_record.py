"""CLI: write OV-SEL-CT10-01 independent anchor selection verdict lock."""

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

from formal.python.toe.observables.ovselct10_independent_anchor_selection_verdict_record import (
    ovselct10_selection_verdict_record,
    write_ovselct10_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--status-date", default="2026-02-12")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")
    args = p.parse_args(argv)

    rec = ovselct10_selection_verdict_record(status_date=str(args.status_date))

    if not args.no_write:
        path = write_ovselct10_lock(status_date=str(args.status_date))
        if args.report:
            print(f"Wrote lock: {path}")

    if args.report:
        print("OV-SEL-CT10-01 report")
        print(f"  schema: {rec.schema}")
        print(f"  verdict: {rec.verdict}")
        print(f"  failed_checks: {len(rec.failed_checks)}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
