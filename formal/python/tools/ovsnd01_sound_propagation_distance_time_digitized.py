"""CLI: write OV-SND-01N digitized artifacts + computed lock."""

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

from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import (
    ovsnd01_digitized_propagation_dataset_record,
    write_ovsnd01_digitized_artifacts,
    write_ovsnd01_digitized_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-24")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovsnd01_digitized_propagation_dataset_record(date=str(args.date))

    if not args.no_write:
        paths = write_ovsnd01_digitized_artifacts(date=str(args.date))
        lock = write_ovsnd01_digitized_lock(date=str(args.date))
        if args.report:
            print(f"Wrote artifacts: {paths}")
            print(f"Wrote lock: {lock}")

    if args.report:
        print("OV-SND-01N report")
        print(f"  schema: {rec.schema}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print(f"  csv_sha256: {rec.dataset['csv_sha256']}")
        print(f"  row_count: {rec.dataset['row_count']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
