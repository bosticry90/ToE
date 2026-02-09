"""CLI wrapper for OV-BR-SND-02 cross-source density mapping record lock."""

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

from formal.python.toe.observables.ovbr_snd02_cross_source_density_mapping_record import (
    ovbr_snd02_cross_source_density_mapping_record,
    write_ovbr_snd02_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument("--lock-path", default=None, help="Override lock output path")
    p.add_argument("--date", default="2026-01-24", help="Date string to embed in the record")

    args = p.parse_args(argv)

    rec = ovbr_snd02_cross_source_density_mapping_record(date=str(args.date))

    if not args.no_write:
        out = write_ovbr_snd02_lock(
            lock_path=Path(args.lock_path) if args.lock_path is not None else None,
            date=str(args.date),
        )
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-BR-SND-02 report")
        print(f"  schema: {rec.schema}")
        print(f"  date: {rec.date}")
        print(f"  mapping_status: {rec.mapping['status']}")
        print(f"  blockers: {rec.mapping['current_blockers']}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
