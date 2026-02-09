"""CLI: write OV-SEL-BM-03 numeric benchmark ingestion audit lock (OV-BM-02N)."""

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

from formal.python.toe.observables.ovselbm03_numeric_benchmark_ingestion_audit_ovbm02n_record import (
    ovselbm03_numeric_benchmark_ingestion_record,
    write_ovselbm03_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--status-date", default="2026-01-24")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovselbm03_numeric_benchmark_ingestion_record(status_date=str(args.status_date))

    if not args.no_write:
        lock = write_ovselbm03_lock(status_date=str(args.status_date))
        if args.report:
            print(f"Wrote lock: {lock}")

    if args.report:
        print("OV-SEL-BM-03 report")
        print(f"  schema: {rec.schema}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print(f"  benchmark: {rec.benchmark_numeric['digitization_id']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
