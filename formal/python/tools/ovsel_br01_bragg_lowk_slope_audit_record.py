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

from formal.python.toe.observables.ovsel_br01_bragg_lowk_slope_audit_record import (
    ovsel_br01_bragg_lowk_slope_audit_record,
    write_ovsel_br01_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--status-date", default="2026-01-25")
    p.add_argument("--write-lock", action="store_true")
    p.add_argument("--report", action="store_true")
    args = p.parse_args(argv)

    rec = ovsel_br01_bragg_lowk_slope_audit_record(status_date=str(args.status_date))
    if args.report:
        print(rec.to_jsonable())

    if args.write_lock:
        out = write_ovsel_br01_lock(status_date=str(args.status_date))
        if args.report:
            print(f"wrote: {out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
