"""CLI for OV-DQ-02: DQ-01_v2 threshold update policy lock."""

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

from formal.python.toe.observables.ovdq02_dq01_v2_threshold_update_record import (
    ovdq02_dq01_v2_threshold_update_record,
    write_ovdq02_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--write-lock", action="store_true", help="Write/update the markdown policy lock")
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument("--lock-path", default=None, help="Override lock output path")
    p.add_argument("--date", default="2026-01-23", help="Date string to embed in the record")
    p.add_argument("--q-threshold-from", default=0.90, type=float, help="Baseline q_threshold (v1)")
    p.add_argument("--q-threshold-to", default=1.05, type=float, help="Proposed q_threshold (v2)")
    args = p.parse_args(argv)

    rec = None
    if args.report:
        rec = ovdq02_dq01_v2_threshold_update_record(
            date=str(args.date),
            q_threshold_from=float(args.q_threshold_from),
            q_threshold_to=float(args.q_threshold_to),
        )

    if args.write_lock:
        out = write_ovdq02_lock(lock_path=Path(args.lock_path) if args.lock_path is not None else None)
        print(f"Wrote lock: {out}")

    if args.report and rec is not None:
        print("OV-DQ-02 report")
        print(f"  schema: {rec.schema}")
        print(f"  date: {rec.date}")
        print(f"  from_policy: {rec.from_policy}  q_threshold={float(rec.q_threshold_from):.12g}")
        print(f"  to_policy: {rec.to_policy}  q_threshold={float(rec.q_threshold_to):.12g}")
        print(f"  delta.changed_fields: {list(rec.delta.get('changed_fields', []))}")
        print(f"  impact_set: {list(rec.impact_set)}")
        print(f"  evidence_artifact_relpath: {rec.evidence_artifact_relpath}")
        print(f"  evidence_artifact_fingerprint: {rec.evidence_artifact_fingerprint}")
        print(f"  record_fingerprint: {rec.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
