"""CLI wrapper for OV-XD-03 overlap band record.

This tool:
- Computes the OV-XD-03 overlap-band record (pure bookkeeping).
- Optionally writes/updates the canonical markdown lock.
- Prints a deterministic --report summary suitable for audit logs.

Usage
  python -m formal.python.tools.ovxd03_overlap_band_record --report

By default it writes the lock at:
  formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md

Add --no-write to compute/report without touching the lock.
"""

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

from formal.python.toe.observables.ovxd03_overlap_band_record import (
    ovxd03_overlap_band_record,
    write_ovxd03_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--no-write", action="store_true", help="Do not update the markdown lock")
    p.add_argument(
        "--lock-path",
        default=None,
        help="Override lock output path (default: canonical lock in formal/markdown/locks/observables)",
    )

    args = p.parse_args(argv)

    rec = ovxd03_overlap_band_record()

    if not args.no_write:
        lock_path = Path(args.lock_path) if args.lock_path is not None else None
        out = write_ovxd03_lock(lock_path=lock_path)
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-XD-03 report")
        print(f"  schema: {rec.schema}")
        print(f"  included: {', '.join(rec.included_band_ids)}")
        if rec.excluded:
            print("  excluded:")
            for k in sorted(rec.excluded.keys()):
                print(f"    - {k}: {rec.excluded[k]}")
        else:
            print("  excluded: (none)")

        print("  bands:")
        for k in rec.included_band_ids:
            b = rec.bands[k]
            print(f"    - {k}: k_min={b.k_min:.12g}  k_max={b.k_max:.12g}")

        ov = rec.overlap
        print("  overlap:")
        print(f"    k_min={ov.k_min:.12g}  k_max={ov.k_max:.12g}  non_empty={ov.non_empty}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
