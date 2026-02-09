"""CLI wrapper for OV-SND-02B derived speed (seriesB) lock."""

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

from formal.python.toe.observables.ovsnd02b_sound_speed_from_propagation_seriesb_record import (
    ovsnd02b_sound_speed_from_propagation_record,
    write_ovsnd02b_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--date", default="2026-01-24")
    args = p.parse_args(argv)

    if not args.no_write:
        lock = write_ovsnd02b_lock(date=str(args.date))
        if args.report:
            print(f"Wrote lock: {lock}")

    rec = ovsnd02b_sound_speed_from_propagation_record(date=str(args.date))

    if args.report:
        print("OV-SND-02B report")
        print(f"  schema: {rec.schema}")
        print(f"  date: {rec.date}")
        print(f"  blocked: {rec.status['blocked']}")
        print(f"  blockers: {rec.status['blockers']}")
        if rec.results is not None:
            c = rec.results.get("primary", {}).get("c_m_per_s")
            se = rec.results.get("primary", {}).get("se_m_per_s")
            print(f"  c_m_per_s: {c}")
            print(f"  se_m_per_s: {se}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
