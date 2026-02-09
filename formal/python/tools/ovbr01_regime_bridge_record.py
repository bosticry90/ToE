"""CLI wrapper for OV-BR-01 regime bridge record.

This tool:
- Computes OV-BR-01 (pure bookkeeping; no fitting across regimes).
- Optionally writes/updates the canonical markdown lock.
- Prints a deterministic --report summary suitable for audit logs.

Usage
  python -m formal.python.tools.ovbr01_regime_bridge_record --report

By default it writes the lock at:
  formal/markdown/locks/observables/OV-BR-01_regime_bridge_record.md

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

from formal.python.toe.observables.ovbr01_regime_bridge_record import (
    ovbr01_regime_bridge_record,
    write_ovbr01_lock,
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

    rec = ovbr01_regime_bridge_record()

    if not args.no_write:
        lock_path = Path(args.lock_path) if args.lock_path is not None else None
        out = write_ovbr01_lock(lock_path=lock_path)
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print("OV-BR-01 report")
        print(f"  schema: {rec.schema}")
        lb0, lb1 = rec.low_band
        hb0, hb1 = rec.high_band
        print(f"  low_band (OV-01g): k=[{lb0:.12g}, {lb1:.12g}]")
        print(f"  high_band (OV-03x): k=[{hb0:.12g}, {hb1:.12g}]")

        if rec.overlap is not None:
            ok0, ok1 = rec.overlap
            print(f"  overlap: k=[{ok0:.12g}, {ok1:.12g}]")
        else:
            print("  overlap: (none)")

        if rec.gap is not None:
            g0, g1 = rec.gap
            print(f"  gap: k=[{g0:.12g}, {g1:.12g}]  width={float(rec.gap_width):.12g}")
        else:
            print("  gap: (none)")

        lp = rec.low_preference or {}
        hp = rec.high_preference or {}

        print("  low_preference (OV-01g):")
        print(
            "    prefer_curved="
            f"{bool(lp.get('prefer_curved'))}  "
            "robustness_failed="
            f"{bool(lp.get('robustness_failed'))}  "
            "adequacy_policy="
            f"{str(lp.get('adequacy_policy', 'unknown'))}"
        )
        if lp.get("report_fingerprint") is not None:
            print(f"    report_fingerprint={lp['report_fingerprint']}")

        print("  high_preference (OV-03x):")
        print(
            "    prefer_curved="
            f"{bool(hp.get('prefer_curved'))}  "
            "robustness_failed="
            f"{bool(hp.get('robustness_failed'))}  "
            "adequacy_policy="
            f"{str(hp.get('adequacy_policy', 'unknown'))}"
        )
        if hp.get("report_fingerprint") is not None:
            print(f"    report_fingerprint={hp['report_fingerprint']}")

        print("  comparability_statement:")
        print(f"    {rec.comparability_statement}")

        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
