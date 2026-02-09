"""CLI wrapper for OV-04x fit-family robustness record (DS-02 low-k).

This tool:
- Computes OV-04x robustness-only report from frozen DS-02 artifacts.
- Optionally writes/updates the canonical markdown lock.
- Prints a deterministic --report summary suitable for audit logs.

Usage
  python -m formal.python.tools.ov04x_fit_family_robustness_record --report

By default it writes the lock at:
  formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md

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

from formal.python.toe.observables.ov04x_fit_family_robustness_record import (
    ov04x_fit_family_robustness_report,
    write_ov04x_lock,
)
from formal.python.toe.observables.ov01_fit_family_robustness import ov01_fit_family_robustness_failure_reasons


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
        help="Adequacy policy string passed to the robustness gate",
    )
    p.add_argument(
        "--q-threshold",
        default=0.90,
        type=float,
        help="q_threshold passed to the robustness gate",
    )

    args = p.parse_args(argv)

    rep = ov04x_fit_family_robustness_report(
        adequacy_policy=str(args.adequacy_policy),
        q_threshold=float(args.q_threshold),
        config_tag=f"OV-04x_fit_family_robustness_{str(args.adequacy_policy)}_q{float(args.q_threshold):.12g}",
    )

    if not args.no_write:
        lock_path = Path(args.lock_path) if args.lock_path is not None else None
        out = write_ov04x_lock(
            lock_path=lock_path,
            adequacy_policy=str(args.adequacy_policy),
            q_threshold=float(args.q_threshold),
            config_tag=f"OV-04x_fit_family_robustness_{str(args.adequacy_policy)}_q{float(args.q_threshold):.12g}",
        )
        if args.report:
            print(f"Wrote lock: {out}")

    if args.report:
        print(
            "OV-04x report (DS-02 low-k) "
            f"[adequacy_policy={str(args.adequacy_policy)}, q_threshold={float(args.q_threshold):.12g}]"
        )
        print(f"  config_tag: {rep.config_tag}")
        print(f"  adequacy_policy: {rep.adequacy_policy}")
        print(f"  prefer_curved: {bool(rep.prefer_curved)}")
        print(f"  robustness_failed: {bool(rep.robustness_failed)}")
        reasons = ov01_fit_family_robustness_failure_reasons(rep)
        print(f"  failure_reasons: {reasons if reasons else '[]'}")
        print(f"  curved_adequacy_passes: {bool(rep.curved_adequacy_passes)}")
        print(f"  q_ratio: {float(rep.q_ratio):.12g}  q_threshold: {float(rep.q_threshold):.12g}")
        if not (float(rep.r_max_linear) == 0.0):
            print(f"  q_ratio<=threshold: {bool(float(rep.q_ratio) <= float(rep.q_threshold))}")
        print(
            "  R_max linear/curved: "
            f"{float(rep.r_max_linear):.12g} / {float(rep.r_max_curved):.12g}"
        )
        print(f"  report_fingerprint: {rep.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
