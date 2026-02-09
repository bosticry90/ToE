"""CLI wrapper for OV-SEL-BM-04 benchmark interaction stress-test lock."""

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

from formal.python.toe.observables.ovselbm04_benchmark_interaction_stress_test_record import (
    ovselbm04_benchmark_interaction_stress_test_record,
    write_ovselbm04_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--status-date", default="2026-01-23")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovselbm04_benchmark_interaction_stress_test_record(status_date=str(args.status_date))

    if not args.no_write:
        out = write_ovselbm04_lock(status_date=str(args.status_date))
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-SEL-BM-04 report")
        print(f"  schema: {rec.schema}")
        print(f"  status_date: {rec.status_date}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
