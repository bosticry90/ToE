"""CLI wrapper for OV-SND-03N central density digitization (artifacts + lock)."""

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

from formal.python.toe.observables.ovsnd03n_central_density_digitized import (
    ovsnd03n_central_density_digitized_record,
    write_ovsnd03n_digitized_artifacts,
    write_ovsnd03n_digitized_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update artifacts/lock")
    p.add_argument("--date", default="2026-01-24", help="Date string to embed in the record")

    args = p.parse_args(argv)

    rec = ovsnd03n_central_density_digitized_record(date=str(args.date))

    if not args.no_write:
        paths = write_ovsnd03n_digitized_artifacts(date=str(args.date))
        lock_path = write_ovsnd03n_digitized_lock(date=str(args.date))
        if args.report:
            print(f"Wrote artifacts: {paths}")
            print(f"Wrote lock: {lock_path}")

    if args.report:
        print("OV-SND-03N report")
        print(f"  schema: {rec.schema}")
        print(f"  date: {rec.date}")
        print(f"  digitization_id: {rec.digitization_id}")
        print(f"  n_rows: {rec.dataset['row_count']}")
        print(f"  pdf_sha256: {rec.source['arxiv_pdf_sha256']}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
