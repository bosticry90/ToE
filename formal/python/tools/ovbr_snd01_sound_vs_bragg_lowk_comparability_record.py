"""CLI: write OV-BR-SND-01 sound-vs-Bragg comparability lock."""

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

from formal.python.toe.observables.ovbr_snd01_sound_vs_bragg_lowk_comparability_record import (
    ovbr_snd01_sound_vs_bragg_lowk_comparability_record,
    write_ovbr_snd01_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-24")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovbr_snd01_sound_vs_bragg_lowk_comparability_record(date=str(args.date))

    if not args.no_write:
        path = write_ovbr_snd01_lock(date=str(args.date))
        if args.report:
            print(f"Wrote lock: {path}")

    if args.report:
        print("OV-BR-SND-01 report")
        print(f"  schema: {rec.schema}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print(f"  status: {rec.comparability['status']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
