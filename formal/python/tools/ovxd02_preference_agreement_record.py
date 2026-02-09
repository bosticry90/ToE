"""CLI wrapper for OV-XD-02 cross-dataset preference agreement record.

This tool:
- Computes OV-XD-02 (bookkeeping record; computed from frozen artifacts).
- Optionally writes/updates the canonical markdown lock.
- Prints a deterministic --report summary suitable for audit logs.

Usage
  python -m formal.python.tools.ovxd02_preference_agreement_record --report

By default it writes the lock at:
  formal/markdown/locks/observables/OV-XD-02_cross_dataset_preference_agreement_record.md

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

from formal.python.toe.observables.ovxd02_preference_agreement_record_lock import (
    compute_ovxd02_record,
    write_ovxd02_lock,
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

    rec = compute_ovxd02_record()

    if not args.no_write:
        lock_path = Path(args.lock_path) if args.lock_path is not None else None
        out = write_ovxd02_lock(lock_path=lock_path)
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-XD-02 report")
        print(f"  config_tag: {rec.config_tag}")
        print(f"  ov01g_report_fingerprint: {rec.ov01g_report_fingerprint}")
        print(f"  ov02x_report_fingerprint: {rec.ov02x_report_fingerprint}")
        print(f"  ov03x_report_fingerprint: {rec.ov03x_report_fingerprint}")
        print(f"  ov01g_preferred_family: {rec.ov01g_preferred_family}")
        print(f"  ov03x_preferred_family: {rec.ov03x_preferred_family}")
        print(f"  ov02x_all_scenarios_match_baseline: {bool(rec.ov02x_all_scenarios_match_baseline)}")
        print(f"  agreement: {bool(rec.agreement)}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
