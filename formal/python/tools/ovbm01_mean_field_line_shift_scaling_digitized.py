"""CLI: write OV-BM-01N digitized benchmark artifacts + computed lock."""

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

from formal.python.toe.observables.ovbm01_mean_field_line_shift_scaling_digitized import (
    write_ovbm01_digitized_artifacts,
    write_ovbm01_digitized_lock,
    ovbm01_digitized_mean_shift_dataset_record,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-23")
    p.add_argument("--no-write", action="store_true", help="Do not write artifacts/lock")
    p.add_argument("--report", action="store_true", help="Print a short report")

    args = p.parse_args(argv)

    rec = ovbm01_digitized_mean_shift_dataset_record(date=str(args.date))

    if not args.no_write:
        outs = write_ovbm01_digitized_artifacts(date=str(args.date))
        lock = write_ovbm01_digitized_lock(date=str(args.date))
        if args.report:
            print(f"Wrote CSV: {outs['csv']}")
            print(f"Wrote metadata: {outs['metadata']}")
            print(f"Wrote lock: {lock}")

    if args.report:
        print("OV-BM-01N report")
        print(f"  schema: {rec.schema}")
        print(f"  digitization_id: {rec.digitization_id}")
        print(f"  rows: {rec.dataset.get('row_count')}")
        print(f"  csv_sha256: {rec.dataset.get('csv_sha256')}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
