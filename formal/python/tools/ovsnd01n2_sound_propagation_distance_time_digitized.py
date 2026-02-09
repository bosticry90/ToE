"""CLI wrapper for OV-SND-01N2 second propagation series lock."""

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

from formal.python.toe.observables.ovsnd01n2_sound_propagation_distance_time_digitized import (
    ovsnd01n2_digitized_propagation_dataset_record,
    write_ovsnd01n2_digitized_artifacts,
    write_ovsnd01n2_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--date", default="2026-01-24")
    args = p.parse_args(argv)

    if not args.no_write:
        _ = write_ovsnd01n2_digitized_artifacts(date=str(args.date))
        lock = write_ovsnd01n2_lock(date=str(args.date))
        if args.report:
            print(f"Wrote lock: {lock}")

    rec = ovsnd01n2_digitized_propagation_dataset_record(date=str(args.date))

    if args.report:
        print("OV-SND-01N2 report")
        print(f"  schema: {rec.schema}")
        print(f"  date: {rec.date}")
        print(f"  blocked: {rec.status['blocked']}")
        print(f"  blockers: {rec.status['blockers']}")
        if rec.dataset is not None:
            sA = rec.dataset.get("seriesA")
            sB = rec.dataset.get("seriesB")
            if isinstance(sA, dict) and isinstance(sB, dict):
                print(f"  seriesA_row_count: {sA.get('row_count')}")
                print(f"  seriesB_row_count: {sB.get('row_count')}")
            split = rec.dataset.get("split_rule")
            if isinstance(split, dict):
                print(f"  split_rule_id: {split.get('rule_id')}")
                print(f"  largest_gap_ms: {split.get('largest_gap_ms')}")
                print(f"  gap_index: {split.get('gap_index')}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
