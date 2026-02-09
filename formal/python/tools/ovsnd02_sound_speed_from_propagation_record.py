"""CLI: write OV-SND-02 derived sound-speed lock."""

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

from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import (
    ovsnd02_sound_speed_from_propagation_record,
    write_ovsnd02_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-24")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovsnd02_sound_speed_from_propagation_record(date=str(args.date))

    if not args.no_write:
        path = write_ovsnd02_lock(date=str(args.date))
        if args.report:
            print(f"Wrote lock: {path}")

    if args.report:
        c = rec.results["primary"]["c_m_per_s"]
        se = rec.results["primary"]["se_m_per_s"]
        print("OV-SND-02 report")
        print(f"  schema: {rec.schema}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print(f"  c_m_per_s: {c}")
        print(f"  se_m_per_s: {se}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
