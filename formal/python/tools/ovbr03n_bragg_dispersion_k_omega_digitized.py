"""CLI wrapper for OV-BR-03N digitized Bragg dispersion ω(k)."""

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

from formal.python.toe.observables.ovbr03n_bragg_dispersion_k_omega_digitized import (
    write_ovbr03n_digitized_artifacts,
    write_ovbr03n_digitized_lock,
)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-25")
    p.add_argument("--artifacts-only", action="store_true")
    p.add_argument("--force-redigitize", action="store_true")

    args = p.parse_args(argv)

    _ = write_ovbr03n_digitized_artifacts(date=str(args.date), force_redigitize=bool(args.force_redigitize))

    if not bool(args.artifacts_only):
        _ = write_ovbr03n_digitized_lock(date=str(args.date))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
