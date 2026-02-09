"""Generate frozen DR window artifacts from an external omega(k) digitization CSV.

This is a generalized version of the Steinhauer-specific generator.

Design goals
- Deterministic: no RNG, stable ordering.
- Evidence-friendly: emits the same fields the repository's frozen artifacts use.
- Minimal dependencies: uses in-repo DR/DQ/BR helpers, plus stdlib.

This script does NOT overwrite existing files unless --force is provided.

CSV schema
- Must provide columns:
  - source
  - figure
  - k_um_inv
  - omega_over_2pi_kHz

Optional columns (ignored by this generator)
- sigma_k_um_inv
- sigma_omega_over_2pi_kHz
- notes

Typical usage
- Inspect available k values:
    python -m formal.python.tools.generate_external_dr_artifacts window-counts \
      --csv formal/external_evidence/<dataset>/omega_k_data.csv \
      --figure Fig3a

- Generate one linear+curved DR window artifact pair:
    python -m formal.python.tools.generate_external_dr_artifacts generate \
      --csv formal/external_evidence/<dataset>/omega_k_data.csv \
      --figure Fig3a \
      --kmax-um-inv 2.5 \
      --out-linear formal/external_evidence/<dataset>/dr01_fit_artifact.json \
      --out-curved formal/external_evidence/<dataset>/dr01_fit_artifact_curved.json \
      --tag DR01_<dataset>_kmax_2p5
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
import csv
import json
import math
import sys
from dataclasses import asdict
from pathlib import Path


def _omega_over_2pi_units_scale_to_hz(units: str) -> float:
    u = str(units).strip().lower()
    if u in {"khz", "k"}:
        return 1.0e3
    if u in {"hz"}:
        return 1.0
    raise ValueError(f"Unsupported --omega-over-2pi-units: {units!r} (expected 'Hz' or 'kHz')")


def _ensure_repo_root_on_syspath() -> None:
    p = Path(__file__).resolve()
    while p != p.parent:
        if (p / "formal").exists():
            repo_root = p
            if str(repo_root) not in sys.path:
                sys.path.insert(0, str(repo_root))
            return
        p = p.parent


_ensure_repo_root_on_syspath()

from formal.python.toe.bridges.br01_dispersion_to_metric import br01_metric_from_DR01_fit, br01_metric_from_DR01_fit_curved
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import dr01_fit_curved_from_sample_kw
from formal.python.toe.dr01_fit_quality import dr01_quality_through_origin_from_sample_kw


def _load_rows(csv_path: Path, *, figure: str | None) -> list[dict[str, str]]:
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows = [r for r in reader]

    if figure is not None:
        rows = [r for r in rows if (r.get("figure", "").strip() == str(figure))]

    if not rows:
        raise RuntimeError(f"No rows found in {csv_path} for figure={figure!r}")
    return rows


def _sample_kw_for_kmax(
    csv_path: Path,
    *,
    kmax_um_inv: float,
    figure: str | None,
    omega_over_2pi_units: str,
) -> tuple[tuple[float, float], ...]:
    rows = _load_rows(csv_path, figure=figure)

    f_scale_to_hz = _omega_over_2pi_units_scale_to_hz(omega_over_2pi_units)

    items: list[tuple[float, float]] = []
    for r in rows:
        k_um = float(r["k_um_inv"])
        if k_um <= float(kmax_um_inv) + 1e-12:
            f_raw = float(r["omega_over_2pi_kHz"])
            k_m_inv = k_um * 1.0e6
            omega_rad_s = 2.0 * math.pi * (f_raw * f_scale_to_hz)
            items.append((k_m_inv, omega_rad_s))

    items.sort(key=lambda t: (t[0], t[1]))
    if len(items) < 2:
        raise ValueError("Need at least 2 points for a linear through-origin fit")

    return tuple(items)


def _fit_through_origin(sample_kw: tuple[tuple[float, float], ...]) -> float:
    sxx = sum(k * k for (k, _) in sample_kw)
    if sxx == 0.0:
        raise ValueError("Degenerate sample: sum(k^2) == 0")
    sxy = sum(k * w for (k, w) in sample_kw)
    return float(sxy / sxx)


def _metric_1d_fields_from_dr_fit(dr01_fit: DR01Fit1D) -> dict[str, float]:
    metric = br01_metric_from_DR01_fit(dr01_fit, n=1)
    return {
        "c_s2": float(metric.c_s2.ravel()[0]),
        "g_tt": float(metric.g_tt.ravel()[0]),
        "g_tx": float(metric.g_tx.ravel()[0]),
        "g_xx": float(metric.g_xx.ravel()[0]),
    }


def _metric_1d_fields_from_dr_fit_curved(dr01_fit_curved) -> dict[str, float]:
    metric = br01_metric_from_DR01_fit_curved(dr01_fit_curved, n=1)
    return {
        "c_s2": float(metric.c_s2.ravel()[0]),
        "g_tt": float(metric.g_tt.ravel()[0]),
        "g_tx": float(metric.g_tx.ravel()[0]),
        "g_xx": float(metric.g_xx.ravel()[0]),
    }


def _write_json(path: Path, payload: dict, *, force: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and not force:
        raise FileExistsError(f"Refusing to overwrite existing file: {path} (use --force)")
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def cmd_window_counts(args: argparse.Namespace) -> None:
    csv_path = Path(args.csv)
    rows = _load_rows(csv_path, figure=args.figure)

    ks = sorted(float(r["k_um_inv"]) for r in rows)
    print(f"Points: N={len(ks)} (figure={args.figure!r})")
    print("k values (um^-1):")
    print(", ".join(f"{k:.6g}" for k in ks))

    thresholds = [1.6, 1.75, 2.1, 2.5, 3.2]
    print("\nCounts by kmax:")
    for t in thresholds:
        n = sum(1 for k in ks if k <= t + 1e-12)
        print(f"  k<= {t}: N={n}")

    for kmax in ks:
        n = sum(1 for k in ks if k <= kmax + 1e-12)
        if n >= 5:
            print(f"\nSmallest kmax for N>=5: {kmax:.17g} (N={n})")
            break


def cmd_generate(args: argparse.Namespace) -> None:
    csv_path = Path(args.csv)

    sample_kw = _sample_kw_for_kmax(
        csv_path,
        kmax_um_inv=float(args.kmax_um_inv),
        figure=args.figure,
        omega_over_2pi_units=str(args.omega_over_2pi_units),
    )

    # Linear artifact (u fixed to 0)
    c_s = _fit_through_origin(sample_kw)
    q = dr01_quality_through_origin_from_sample_kw(sample_kw)

    linear_fit = DR01Fit1D(
        u=0.0,
        c_s=float(c_s),
        tag=str(args.tag),
        source_kind="csv",
        source_ref=str(args.source_ref),
        fit_method_tag=str(args.fit_method_tag),
        sample_kw=sample_kw,
    )

    linear_payload = {
        "u": float(linear_fit.u),
        "c_s": float(linear_fit.c_s),
        "tag": str(linear_fit.tag),
        "source_kind": str(linear_fit.source_kind),
        "source_ref": linear_fit.source_ref,
        "fit_method_tag": str(linear_fit.fit_method_tag),
        "sample_kw": [[float(k), float(w)] for (k, w) in sample_kw],
        "data_fingerprint": str(linear_fit.data_fingerprint),
        "fit_quality": asdict(q),
        "fit_quality_fingerprint": q.fingerprint(),
        "br01_metric_1d": _metric_1d_fields_from_dr_fit(linear_fit),
    }

    # Curved artifact
    curved_fit = dr01_fit_curved_from_sample_kw(
        sample_kw,
        u_fixed=0.0,
        tag=str(args.tag_curved or (str(args.tag) + "_curved")),
        source_kind="csv",
        source_ref=str(args.source_ref_curved or args.source_ref),
        fit_method_tag=str(args.fit_method_tag_curved),
    )

    if curved_fit.fit_quality is None:
        raise RuntimeError("Expected curved_fit.fit_quality to be stamped")

    curved_payload = {
        "u": float(curved_fit.u),
        "c0": float(curved_fit.c0),
        "beta": float(curved_fit.beta),
        "tag": str(curved_fit.tag),
        "source_kind": str(curved_fit.source_kind),
        "source_ref": curved_fit.source_ref,
        "fit_method_tag": str(curved_fit.fit_method_tag),
        "sample_kw": [[float(k), float(w)] for (k, w) in sample_kw],
        "data_fingerprint": str(curved_fit.data_fingerprint),
        "fit_quality": asdict(curved_fit.fit_quality),
        "fit_quality_fingerprint": str(curved_fit.fit_quality_fingerprint),
        "br01_metric_1d": _metric_1d_fields_from_dr_fit_curved(curved_fit),
    }

    _write_json(Path(args.out_linear), linear_payload, force=bool(args.force))
    _write_json(Path(args.out_curved), curved_payload, force=bool(args.force))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_counts = sub.add_parser("window-counts", help="Print k-values and counts by kmax")
    p_counts.add_argument("--csv", required=True)
    p_counts.add_argument("--figure", default=None)
    p_counts.set_defaults(func=cmd_window_counts)

    p_gen = sub.add_parser("generate", help="Generate one linear+curved DR window artifact pair")
    p_gen.add_argument("--csv", required=True)
    p_gen.add_argument("--figure", default=None)
    p_gen.add_argument("--kmax-um-inv", type=float, required=True)
    p_gen.add_argument("--out-linear", required=True)
    p_gen.add_argument("--out-curved", required=True)
    p_gen.add_argument("--tag", required=True)
    p_gen.add_argument("--tag-curved", default=None)
    p_gen.add_argument("--source-ref", default="external digitization CSV")
    p_gen.add_argument("--source-ref-curved", default=None)
    p_gen.add_argument("--fit-method-tag", default="low-k through-origin omega~=c_s*k; u fixed to 0")
    p_gen.add_argument("--fit-method-tag-curved", default="low-k curved omega/k = c0 + beta*k^2; u fixed to 0")
    p_gen.add_argument(
        "--omega-over-2pi-units",
        default="kHz",
        help=(
            "Units of the omega_over_2pi_kHz column values; affects omega conversion via omega=2*pi*f. "
            "Accepted: 'Hz' or 'kHz' (default: kHz for backward compatibility)."
        ),
    )
    p_gen.add_argument("--force", action="store_true")
    p_gen.set_defaults(func=cmd_generate)

    args = parser.parse_args(argv)
    args.func(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
