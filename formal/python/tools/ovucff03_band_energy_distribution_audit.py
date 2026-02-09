"""CLI for OV-UCFF-03 band energy distribution audit scaffold.

Usage
  .\py.ps1 -m formal.python.tools.ovucff03_band_energy_distribution_audit --report --demo noise
  .\py.ps1 -m formal.python.tools.ovucff03_band_energy_distribution_audit --report --pinned
  .\py.ps1 -m formal.python.tools.ovucff03_band_energy_distribution_audit --write

Optional
  Provide X via JSON:
    {"X": [[...], [...], ...]}

  .\py.ps1 -m formal.python.tools.ovucff03_band_energy_distribution_audit --report --input-json path/to/x.json

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

from formal.python.toe.observables.ovucff03_band_energy_distribution_audit import (
    default_demo_inputs,
    default_pinned_input_path,
    load_pinned_input_payload,
    ovucff03_band_energy_distribution_audit,
    write_ovucff03_band_energy_distribution_artifact,
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
            "Use the canonical pinned input artifact for OV-UCFF-03. "
            "Ignored if --input-json is provided."
        ),
    )
    p.add_argument("--demo", default="noise", choices=["dc", "noise"], help="Demo input selection")
    p.add_argument("--n-bands", type=int, default=8, help="Number of rFFT bands")
    p.add_argument("--dx", type=float, default=None, help="Spatial bin width (optional; needed for legacy k-based band partition)")
    p.add_argument("--k-low", type=float, default=None, help="Legacy 3-band partition: low/mid boundary (optional)")
    p.add_argument("--k-mid", type=float, default=None, help="Legacy 3-band partition: mid/high boundary (optional)")
    p.add_argument("--eps", type=float, default=1e-12)
    p.add_argument("--report", action="store_true", help="Print the JSON report")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.report:
        if args.input_json:
            X = _load_X(Path(args.input_json))
            dx = args.dx
        elif args.pinned:
            pinned = load_pinned_input_payload(path=default_pinned_input_path())
            X = pinned["X"]
            dx = pinned["dx"] if args.dx is None else args.dx
        else:
            X = default_demo_inputs()[str(args.demo)]
            dx = args.dx

        # If the user requests legacy partition but didn't specify k thresholds,
        # default to the locked turbulence diagnostics example thresholds.
        k_low = args.k_low
        k_mid = args.k_mid
        if (k_low is None) != (k_mid is None):
            raise SystemExit("Provide both --k-low and --k-mid (or neither).")
        if args.pinned and k_low is None and k_mid is None:
            k_low, k_mid = 2.0, 6.0

        rep = ovucff03_band_energy_distribution_audit(
            X=X,
            n_bands=int(args.n_bands),
            eps=float(args.eps),
            dx=dx,
            legacy_k_low=k_low,
            legacy_k_mid=k_mid,
        )
        print(json.dumps(rep.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovucff03_band_energy_distribution_artifact()
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
