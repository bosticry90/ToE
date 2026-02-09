"""CLI for OV-UCFF-07 cross-metric coupling audit scaffold.

Usage
  .\py.ps1 -m formal.python.tools.ovucff07_cross_metric_coupling_audit --report --demo mixed
  .\py.ps1 -m formal.python.tools.ovucff07_cross_metric_coupling_audit --report --pinned
  .\py.ps1 -m formal.python.tools.ovucff07_cross_metric_coupling_audit --write

Notes
- Priority: explicit --input-json overrides --pinned.
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
import json
from pathlib import Path

import numpy as np

from formal.python.toe.observables.ovucff07_cross_metric_coupling_audit import (
    default_demo_inputs,
    default_pinned_input_path,
    load_pinned_input_payload,
    ovucff07_cross_metric_coupling_audit,
    write_ovucff07_cross_metric_coupling_artifact,
)


def _load_X(path: Path) -> np.ndarray:
    raw = json.loads(path.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("input JSON must contain key 'X' as a 2D list")
    return np.asarray(X, dtype=float)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input-json", default=None, help="JSON file containing {'X': [[...], ...]} (optional)")
    p.add_argument(
        "--pinned",
        action="store_true",
        help=(
            "Use the canonical pinned input artifact for OV-UCFF-07. "
            "Ignored if --input-json is provided."
        ),
    )
    p.add_argument("--demo", default="mixed", choices=["constant", "mixed", "noise"], help="Demo input selection")
    p.add_argument("--n-bands", type=int, default=8, help="Number of rFFT bands")
    p.add_argument("--dt", type=float, default=None, help="Frame spacing (time step); defaults to pinned dt when --pinned")
    p.add_argument("--max-lag", type=int, default=4, help="Max lag for lag-scan correlation")
    p.add_argument("--eps", type=float, default=1e-12)
    p.add_argument("--report", action="store_true", help="Print the JSON report")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.report:
        if args.input_json:
            X = _load_X(Path(args.input_json))
            dt = 1.0 if args.dt is None else float(args.dt)
        elif args.pinned:
            pinned = load_pinned_input_payload(path=default_pinned_input_path())
            X = pinned["X"]
            dt = pinned["dt"] if args.dt is None else float(args.dt)
        else:
            X = default_demo_inputs()[str(args.demo)]
            dt = 1.0 if args.dt is None else float(args.dt)

        rep = ovucff07_cross_metric_coupling_audit(
            X=X,
            n_bands=int(args.n_bands),
            dt=float(dt),
            max_lag=int(args.max_lag),
            eps=float(args.eps),
        )
        print(json.dumps(rep.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovucff07_cross_metric_coupling_artifact()
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
