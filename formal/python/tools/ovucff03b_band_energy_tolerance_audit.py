"""CLI for OV-UCFF-03B band energy tolerance audit.

Usage
  .\py.ps1 -m formal.python.tools.ovucff03b_band_energy_tolerance_audit --report
  .\py.ps1 -m formal.python.tools.ovucff03b_band_energy_tolerance_audit --write

Reference management (maintenance)
  .\py.ps1 -m formal.python.tools.ovucff03b_band_energy_tolerance_audit --write-reference

Notes
- Priority: explicit --input-json overrides --pinned.
- Priority: explicit --reference-json overrides --pinned-reference.
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
    default_pinned_input_path as ovucff03_default_pinned_input_path,
    load_pinned_input_payload as ovucff03_load_pinned_input_payload,
    ovucff03_band_energy_distribution_audit,
)
from formal.python.toe.observables.ovucff03b_band_energy_tolerance_audit import (
    default_reference_report_path,
    load_reference_report,
    ovucff03b_tolerance_check,
    write_ovucff03b_band_energy_tolerance_artifact,
    write_reference_report_from_ovucff03,
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

    p.add_argument("--reference-json", default=None, help="Reference report JSON (OV-UCFF-03B/reference_report/v1)")
    p.add_argument(
        "--pinned-reference",
        action="store_true",
        help=(
            "Use the canonical pinned reference report for OV-UCFF-03B. "
            "Ignored if --reference-json is provided."
        ),
    )

    p.add_argument("--n-bands", type=int, default=8, help="Number of rFFT bands")
    p.add_argument("--dx", type=float, default=None, help="Spatial bin width (optional; used for legacy k-based band partition)")
    p.add_argument("--k-low", type=float, default=None, help="Legacy 3-band partition: low/mid boundary (optional)")
    p.add_argument("--k-mid", type=float, default=None, help="Legacy 3-band partition: mid/high boundary (optional)")
    p.add_argument("--eps", type=float, default=1e-12)

    p.add_argument("--rtol", type=float, default=1e-6)
    p.add_argument("--atol", type=float, default=1e-9)

    p.add_argument("--report", action="store_true", help="Print the JSON tolerance check")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    p.add_argument("--write-reference", action="store_true", help="(Maintenance) Write the pinned reference report JSON")

    args = p.parse_args(argv)

    if args.write_reference:
        out = write_reference_report_from_ovucff03()
        print(f"Wrote {out.as_posix()}")

    if args.report:
        # Load reference report
        if args.reference_json:
            ref_path = Path(args.reference_json)
        else:
            # Default to pinned reference path unless explicitly overridden.
            ref_path = default_reference_report_path()
        ref_report = load_reference_report(path=ref_path)

        # Load X
        if args.input_json:
            X = _load_X(Path(args.input_json))
            dx = args.dx
        elif args.pinned:
            pinned = ovucff03_load_pinned_input_payload(path=ovucff03_default_pinned_input_path())
            X = pinned["X"]
            dx = pinned["dx"] if args.dx is None else args.dx
        else:
            X = default_demo_inputs()[str(args.demo)]
            dx = args.dx

        k_low = args.k_low
        k_mid = args.k_mid
        if (k_low is None) != (k_mid is None):
            raise SystemExit("Provide both --k-low and --k-mid (or neither).")
        if args.pinned and k_low is None and k_mid is None:
            k_low, k_mid = 2.0, 6.0

        current = ovucff03_band_energy_distribution_audit(
            X=X,
            n_bands=int(args.n_bands),
            eps=float(args.eps),
            dx=dx,
            legacy_k_low=k_low,
            legacy_k_mid=k_mid,
        ).to_jsonable()

        check = ovucff03b_tolerance_check(
            current_report=current,
            reference_report=ref_report,
            rtol=float(args.rtol),
            atol=float(args.atol),
        )

        print(json.dumps(check.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovucff03b_band_energy_tolerance_artifact(
            rtol=float(args.rtol),
            atol=float(args.atol),
            n_bands=int(args.n_bands),
            eps=float(args.eps),
            legacy_k_low=float(args.k_low) if args.k_low is not None else 2.0,
            legacy_k_mid=float(args.k_mid) if args.k_mid is not None else 6.0,
        )
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write and not args.write_reference:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
