"""CLI wrapper for OV-SEL-BM-01 benchmark ingestion stress-test lock."""

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

from formal.python.toe.observables.ovselbm01_benchmark_ingestion_stress_test_record import (
    ovselbm01_benchmark_ingestion_stress_test_record,
    write_ovselbm01_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument("--lock-path", default=None, help="Override lock output path")
    p.add_argument(
        "--status-date",
        default="2026-01-23",
        help="Status date string to embed in the record (default: 2026-01-23)",
    )

    args = p.parse_args(argv)

    rec = ovselbm01_benchmark_ingestion_stress_test_record(status_date=str(args.status_date))

    if not args.no_write:
        out = write_ovselbm01_lock(
            lock_path=Path(args.lock_path) if args.lock_path is not None else None,
            status_date=str(args.status_date),
        )
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-SEL-BM-01 report")
        print(f"  schema: {rec.schema}")
        print(f"  status_date: {rec.status_date}")
        all_ok = all(bool(v.get('ok')) for v in rec.checks.values())
        print(f"  checks.all_ok: {bool(all_ok)}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print("  narrative:")
        print(rec.narrative)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
