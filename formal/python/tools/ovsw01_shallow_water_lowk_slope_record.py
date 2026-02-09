"""CLI: write OV-SW-01 shallow-water low-k slope lock."""

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

from formal.python.toe.observables.ovsw01_shallow_water_lowk_slope_record import (
    ovsw01_shallow_water_lowk_slope_record,
    write_ovsw01_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-25")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovsw01_shallow_water_lowk_slope_record(date=str(args.date))

    if not args.no_write:
        path = write_ovsw01_lock(date=str(args.date))
        if args.report:
            print(f"Wrote lock: {path}")

    if args.report:
        print("OV-SW-01 report")
        print(f"  schema: {rec.schema}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print(f"  blocked: {bool(rec.status.get('blocked'))}")
        if rec.status.get("blocked"):
            print(f"  blockers: {', '.join(rec.status.get('blockers', []))}")
        else:
            slope = rec.results["primary"]["slope_m_per_s"] if rec.results else None
            se = rec.results["primary"]["se_m_per_s"] if rec.results else None
            print(f"  slope_m_per_s: {slope}")
            print(f"  se_m_per_s: {se}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
