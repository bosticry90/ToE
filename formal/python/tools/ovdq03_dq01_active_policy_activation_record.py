"""CLI: write OV-DQ-03 DQ-01 active policy activation lock."""

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

from formal.python.toe.observables.ovdq03_dq01_active_policy_activation_record import (
    ovdq03_dq01_active_policy_activation_record,
    write_ovdq03_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-24")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovdq03_dq01_active_policy_activation_record(date=str(args.date))

    if not args.no_write:
        lock = write_ovdq03_lock(date=str(args.date))
        if args.report:
            print(f"Wrote lock: {lock}")

    if args.report:
        print("OV-DQ-03 report")
        print(f"  schema: {rec.schema}")
        print(f"  active_policy_id: {rec.active_policy_id}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
