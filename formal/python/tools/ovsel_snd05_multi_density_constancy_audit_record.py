"""CLI wrapper for OV-SEL-SND-05 multi-density constancy audit lock."""

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

from formal.python.toe.observables.ovsel_snd05_multi_density_constancy_audit_record import (
    ovsel_snd05_multi_density_constancy_audit_record,
    write_ovsel_snd05_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument("--lock-path", default=None, help="Override lock output path")
    p.add_argument("--status-date", default="2026-01-24", help="Date string to embed in the record")

    args = p.parse_args(argv)

    rec = ovsel_snd05_multi_density_constancy_audit_record(status_date=str(args.status_date))

    if not args.no_write:
        out = write_ovsel_snd05_lock(
            lock_path=Path(args.lock_path) if args.lock_path is not None else None,
            status_date=str(args.status_date),
        )
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-SEL-SND-05 report")
        print(f"  schema: {rec.schema}")
        print(f"  status_date: {rec.status_date}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        ok = all(bool(v.get('ok', True)) for v in rec.checks.values() if isinstance(v, dict))
        print(f"  checks_ok: {ok}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
