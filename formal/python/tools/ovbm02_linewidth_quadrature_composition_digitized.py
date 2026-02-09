"""CLI: write OV-BM-02N digitized benchmark artifacts + computed lock."""

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

from formal.python.toe.observables.ovbm02_linewidth_quadrature_composition_digitized import (
    ovbm02_digitized_linewidth_dataset_record,
    write_ovbm02_digitized_artifacts,
    write_ovbm02_digitized_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-24")
    p.add_argument("--no-write", action="store_true")
    p.add_argument("--report", action="store_true")

    args = p.parse_args(argv)

    rec = ovbm02_digitized_linewidth_dataset_record(date=str(args.date))

    if not args.no_write:
        paths = write_ovbm02_digitized_artifacts(date=str(args.date))
        lock = write_ovbm02_digitized_lock(date=str(args.date))
        if args.report:
            print(f"Wrote artifacts: {paths}")
            print(f"Wrote lock: {lock}")

    if args.report:
        print("OV-BM-02N report")
        print(f"  schema: {rec.schema}")
        print(f"  digitization_id: {rec.digitization_id}")
        print(f"  record_fingerprint: {rec.fingerprint()}")
        print(f"  csv_sha256: {rec.dataset['csv_sha256']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
