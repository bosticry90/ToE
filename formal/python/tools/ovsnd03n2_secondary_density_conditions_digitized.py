"""CLI wrapper for OV-SND-03N2 secondary density conditions (lock only)."""

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

from formal.python.toe.observables.ovsnd03n2_secondary_density_conditions_digitized import (
    ovsnd03n2_secondary_density_conditions_digitized_record,
    write_ovsnd03n2_digitized_artifacts,
    write_ovsnd03n2_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the lock")
    p.add_argument("--date", default="2026-01-24", help="Date string to embed in the record")

    args = p.parse_args(argv)

    if not args.no_write:
        try:
            paths = write_ovsnd03n2_digitized_artifacts(date=str(args.date))
        except FileNotFoundError:
            paths = None
        lock_path = write_ovsnd03n2_lock(date=str(args.date))
        if args.report:
            if paths is not None:
                print(f"Wrote artifacts: {paths}")
            print(f"Wrote lock: {lock_path}")

    # Always compute the record after any optional write step so reporting is consistent.
    rec = ovsnd03n2_secondary_density_conditions_digitized_record(date=str(args.date))

    if args.report:
        print("OV-SND-03N2 report")
        print(f"  schema: {rec.schema}")
        print(f"  date: {rec.date}")
        print(f"  blocked: {rec.status['blocked']}")
        print(f"  blockers: {rec.status['blockers']}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
