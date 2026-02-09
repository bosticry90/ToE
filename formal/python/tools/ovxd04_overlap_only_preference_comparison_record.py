"""CLI wrapper for OV-XD-04 overlap-only preference comparison record.

This tool:
- Computes OV-XD-04 (pure bookkeeping; overlap-only comparison).
- Optionally writes/updates the canonical markdown lock.
- Prints a deterministic --report summary suitable for audit logs.

Usage
  python -m formal.python.tools.ovxd04_overlap_only_preference_comparison_record --report

By default it writes the lock at:
  formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md

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

from formal.python.toe.observables.ovxd04_overlap_only_preference_comparison_record import (
    ovxd04_overlap_only_preference_comparison_record,
    write_ovxd04_lock,
    write_ovxd04_lock_for_policy,
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
    p.add_argument(
        "--adequacy-policy",
        default="DQ-01_v1",
        help="Curved-fit adequacy policy label (used to select input robustness locks)",
    )
    p.add_argument(
        "--q-threshold",
        default=None,
        type=float,
        help="q_threshold used to select input robustness locks (default depends on --adequacy-policy)",
    )

    args = p.parse_args(argv)

    q_threshold = (
        float(args.q_threshold)
        if args.q_threshold is not None
        else (1.05 if str(args.adequacy_policy) == "DQ-01_v2" else 0.90)
    )

    rec = ovxd04_overlap_only_preference_comparison_record(
        adequacy_policy=str(args.adequacy_policy),
        q_threshold=float(q_threshold),
    )

    if not args.no_write:
        lock_path = Path(args.lock_path) if args.lock_path is not None else None
        out = write_ovxd04_lock_for_policy(
            lock_path=lock_path,
            adequacy_policy=str(args.adequacy_policy),
            q_threshold=float(q_threshold),
        )
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        k0, k1 = rec.overlap_band
        print(
            "OV-XD-04 report "
            f"[adequacy_policy={str(args.adequacy_policy)}, q_threshold={float(q_threshold):.12g}]"
        )
        print(f"  schema: {rec.schema}")
        print(f"  overlap_band: k=[{k0:.12g}, {k1:.12g}]")
        print(
            "  OV-04x preferred_family: "
            f"{rec.low_preferred_family}  (prefer_curved={bool(rec.low_preference.get('prefer_curved'))} "
            f"robustness_failed={bool(rec.low_preference.get('robustness_failed'))})"
        )
        print(
            "  OV-03x preferred_family: "
            f"{rec.high_preferred_family}  (prefer_curved={bool(rec.high_preference.get('prefer_curved'))} "
            f"robustness_failed={bool(rec.high_preference.get('robustness_failed'))})"
        )
        print(f"  agreement: {bool(rec.agreement)}  decisiveness: {rec.decisiveness}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
