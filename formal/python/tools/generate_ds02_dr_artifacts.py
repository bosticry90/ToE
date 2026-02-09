"""Generate DS-02 DR window artifacts from the pinned Shammass Fig. 2 digitization.

This is a thin wrapper around `formal.python.tools.generate_external_dr_artifacts`.

Outputs (written into the DS-02 evidence folder):
- dr01_fit_artifact.json + dr01_fit_artifact_curved.json
- dr03_fit_artifact.json + dr03_fit_artifact_curved.json
- dr04d_fit_artifact.json + dr04d_fit_artifact_curved.json
- dr05_fit_artifact.json + dr05_fit_artifact_curved.json

Window policy (DS-02 specific)
- DR05: k <= 1.8  um^-1
- DR03: k <= 2.1  um^-1
- DR04d: smallest kmax that yields a DQ-01_v1 PASS with N>=8 points
- DR01: k <= 3.33842 um^-1 (forced to reach OV-03x overlap threshold)

Notes
- This script does not digitize the PDF; it consumes omega_k_data.csv.
- It can optionally update DS-02 data_fingerprint.md with csv sha256 + row count.

Usage
  python -m formal.python.tools.generate_ds02_dr_artifacts --force
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
import hashlib
import math
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path


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

from formal.python.tools import generate_external_dr_artifacts

from formal.python.toe.dr01_fit_adequacy import dr01_check_curved_fit_adequacy
from formal.python.toe.dr01_fit_curved import dr01_fit_curved_from_sample_kw


@dataclass(frozen=True)
class WindowSpec:
    window_id: str
    kmax_um_inv: float


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_rows(csv_path: Path, *, figure: str | None, allow_empty: bool = False) -> list[dict[str, str]]:
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows = [r for r in reader]

    if not rows:
        if bool(allow_empty):
            return []
        raise RuntimeError("DS-02 omega_k_data.csv has no rows (still scaffold-only)")

    if figure is not None:
        rows = [r for r in rows if (r.get("figure", "").strip() == str(figure))]
        if not rows:
            if bool(allow_empty):
                return []
            raise RuntimeError(f"No rows found for figure={figure!r}")

    # Minimal schema check.
    required = {"source", "figure", "k_um_inv", "omega_over_2pi_kHz"}
    missing = required - set(rows[0].keys())
    if missing:
        raise RuntimeError(f"CSV missing required columns: {sorted(missing)}")

    # Be robust to accidental row-order edits.
    rows.sort(key=lambda r: float(r["k_um_inv"]))

    # Enforce single-source, single-figure discipline to prevent mixing.
    figures = {str(r.get("figure", "")).strip() for r in rows}
    sources = {str(r.get("source", "")).strip() for r in rows}
    if len(figures) != 1:
        raise RuntimeError(f"Expected a single figure value; got: {sorted(figures)!r}")
    if len(sources) != 1:
        raise RuntimeError(f"Expected a single source value; got: {sorted(sources)!r}")
    if next(iter(sources)) == "":
        raise RuntimeError("CSV 'source' must be non-empty")

    # Numeric hygiene.
    ks = [float(r["k_um_inv"]) for r in rows]
    ws = [float(r["omega_over_2pi_kHz"]) for r in rows]
    if any(k < 0.0 for k in ks):
        raise RuntimeError("CSV contains negative k_um_inv")
    if any(w < 0.0 for w in ws):
        raise RuntimeError("CSV contains negative omega_over_2pi_kHz")

    # Stronger: enforce uniqueness / no duplicates (prevents accidental weighting).
    if any(ks[i] >= ks[i + 1] for i in range(len(ks) - 1)):
        raise RuntimeError("CSV k_um_inv must be strictly increasing (no duplicates)")

    # Sigma columns, if present/filled, must be numeric and non-negative.
    for key in ("sigma_k_um_inv", "sigma_omega_over_2pi_kHz"):
        for r in rows:
            val = str(r.get(key, "")).strip()
            if val == "":
                continue
            if float(val) < 0.0:
                raise RuntimeError(f"CSV {key} must be non-negative")

    # Optional series/marker guard: if a series label column exists, enforce
    # that it reflects the pinned "filled circles" selection.
    for key in ("series", "marker", "legend"):
        if key not in rows[0]:
            continue
        vals = {str(r.get(key, "")).strip().lower() for r in rows}
        if vals == {""}:
            continue
        if len(vals) != 1:
            raise RuntimeError(f"Expected a single {key} label; got: {sorted(vals)!r}")
        v = next(iter(vals))
        if ("filled" not in v) or ("open" in v):
            raise RuntimeError(f"{key} label must indicate filled circles only; got: {v!r}")

    return rows


def _compute_minN5_kmax(ks: list[float]) -> float:
    if len(ks) < 5:
        raise RuntimeError("Need at least 5 points to compute DR04d minN5 window")
    ks_sorted = sorted(ks)
    return float(ks_sorted[4])


def _sample_kw_for_kmax_hz(rows: list[dict[str, str]], *, kmax_um_inv: float) -> tuple[tuple[float, float], ...]:
    # DS-02 column name is legacy (omega_over_2pi_kHz) but values are treated as Hz.
    items: list[tuple[float, float]] = []
    for r in rows:
        k_um = float(r["k_um_inv"])
        if k_um <= float(kmax_um_inv) + 1e-12:
            f_hz = float(r["omega_over_2pi_kHz"])
            k_m_inv = k_um * 1.0e6
            omega_rad_s = 2.0 * math.pi * f_hz
            items.append((k_m_inv, omega_rad_s))

    items.sort(key=lambda t: (t[0], t[1]))
    return tuple(items)


def _compute_dr04d_kmax_adequate(*, rows: list[dict[str, str]], min_points: int = 8) -> float:
    ks = sorted(float(r["k_um_inv"]) for r in rows)
    for kmax in ks:
        sample_kw = _sample_kw_for_kmax_hz(rows, kmax_um_inv=float(kmax))
        if len(sample_kw) < int(min_points):
            continue
        if len(sample_kw) < 3:
            continue

        fit = dr01_fit_curved_from_sample_kw(
            sample_kw,
            u_fixed=0.0,
            tag="DR04d_DS02_window_probe",
            source_kind="csv",
            source_ref="DS-02 omega_k_data.csv",
            fit_method_tag="window probe",
        )
        adequacy = dr01_check_curved_fit_adequacy(fit, policy="DQ-01_v1")
        if bool(adequacy.passes):
            return float(kmax)

    # Fallback: preserve the older behavior for triage if no adequate window exists.
    return _compute_minN5_kmax(ks)


def _default_ds02_paths(repo_root: Path) -> tuple[Path, Path]:
    ds02_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_ds02_lowk_dataset_TBD"
    csv_path = ds02_dir / "omega_k_data.csv"
    return ds02_dir, csv_path


def _render_source_ref(*, csv_path: Path, figure: str | None, kmax_um_inv: float, run_date: str) -> str:
    fig = figure or "(unfiltered)"
    return (
        "Shammass et al. (2012) arXiv:1207.3440v2; "
        "Fig. 2 (filled circles series only); "
        f"{csv_path.as_posix()}; "
        f"low-k window k<= {kmax_um_inv:g} um^-1; "
        "fit through origin; omega=2*pi*f; "
        f"date {run_date}"
    )


def _tag(window_id: str, *, kmax_um_inv: float, run_date: str) -> str:
    k = (f"{kmax_um_inv:.6f}").rstrip("0").rstrip(".")
    k = k.replace(".", "p")
    return f"{window_id}_DS02_Fig2_filled_circles_kmax_{k}_{run_date}"


def _run_generate(
    *,
    csv_path: Path,
    figure: str | None,
    out_linear: Path,
    out_curved: Path,
    kmax_um_inv: float,
    window_id: str,
    run_date: str,
    force: bool,
) -> None:
    src_ref = _render_source_ref(csv_path=csv_path, figure=figure, kmax_um_inv=kmax_um_inv, run_date=run_date)
    argv = [
        "generate",
        "--csv",
        str(csv_path),
        "--kmax-um-inv",
        str(kmax_um_inv),
        "--out-linear",
        str(out_linear),
        "--out-curved",
        str(out_curved),
        "--tag",
        _tag(window_id, kmax_um_inv=kmax_um_inv, run_date=run_date),
        "--source-ref",
        src_ref,
        "--fit-method-tag",
        f"low-k through-origin omega~=c_s*k on k<= {kmax_um_inv:g} um^-1; u fixed to 0",
        "--omega-over-2pi-units",
        "Hz",
    ]
    if figure is not None:
        argv.extend(["--figure", str(figure)])
    if force:
        argv.append("--force")

    # Delegate to the canonical generator.
    generate_external_dr_artifacts.main(argv)


def _replace_or_append_line(text: str, *, prefix: str, new_line: str) -> str:
    out_lines: list[str] = []
    replaced = False
    for ln in text.splitlines():
        if ln.strip().startswith(prefix):
            out_lines.append(new_line)
            replaced = True
        else:
            out_lines.append(ln)
    if not replaced:
        out_lines.append(new_line)
    return "\n".join(out_lines) + "\n"


def _update_data_fingerprint_md(ds02_dir: Path, *, csv_sha256: str, rows: int) -> None:
    fp_path = ds02_dir / "data_fingerprint.md"
    if not fp_path.exists():
        return

    original = fp_path.read_text(encoding="utf-8")

    updated = original
    updated = updated.replace(
        "- omega_k_data.csv sha256: TBD (CSV currently header-only scaffold)",
        f"- omega_k_data.csv sha256: `{csv_sha256}`",
    )
    updated = updated.replace("- rows: TBD", f"- rows: {rows}")

    # Fallback if placeholders drift.
    if updated == original:
        updated = _replace_or_append_line(
            updated,
            prefix="- omega_k_data.csv sha256:",
            new_line=f"- omega_k_data.csv sha256: `{csv_sha256}`",
        )
        updated = _replace_or_append_line(updated, prefix="- rows:", new_line=f"- rows: {rows}")

    if updated != original:
        fp_path.write_text(updated, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--csv",
        default=None,
        help="Path to DS-02 omega_k_data.csv (default: pinned DS-02 folder)",
    )
    parser.add_argument(
        "--figure",
        default="Fig. 2",
        help="Filter by figure value in CSV (default: 'Fig. 2'; set '' to disable)",
    )
    parser.add_argument(
        "--report",
        action="store_true",
        help="Print dataset/window summary and exit (no files written)",
    )
    parser.add_argument("--force", action="store_true", help="Overwrite existing artifact files")
    parser.add_argument(
        "--no-update-fingerprint",
        action="store_true",
        help="Do not update DS-02 data_fingerprint.md with CSV sha256 + row count",
    )
    args = parser.parse_args(argv)

    repo_root = _find_repo_root(Path(__file__))
    ds02_dir, default_csv = _default_ds02_paths(repo_root)

    csv_path = Path(args.csv) if args.csv is not None else default_csv
    if not csv_path.exists():
        raise RuntimeError(f"CSV not found: {csv_path}")

    figure: str | None
    if args.figure is None or str(args.figure).strip() == "":
        figure = None
    else:
        figure = str(args.figure).strip()

    rows = _load_rows(csv_path, figure=figure, allow_empty=bool(args.report))
    if bool(args.report) and not rows:
        fig_msg = figure if figure is not None else "(unfiltered)"
        print(f"DS-02 report: no rows found (figure={fig_msg!r}).")
        print("Populate omega_k_data.csv with digitized points, then re-run --report.")
        return 0

    ks = [float(r["k_um_inv"]) for r in rows]

    kmax_dr01 = 3.33842
    kmax_dr04d = _compute_dr04d_kmax_adequate(rows=rows, min_points=8)

    if bool(args.report):
        kmin = min(ks)
        kmax = max(ks)
        k_lowk_max = 1.5
        n_lowk_required = 10
        n_lowk = sum(1 for k in ks if k <= k_lowk_max)
        print(f"DS-02 rows: N={len(rows)} (figure={figure!r})")
        print(f"k range (um^-1): [{kmin:.6g}, {kmax:.6g}]")
        print(f"low-k density gate: N(k<= {k_lowk_max:g})={n_lowk} (required >= {n_lowk_required})")
        print(
            "overlap reach gate: required max(k) >= "
            f"{kmax_dr01} ; observed max(k)={kmax:.6g} ; passes={kmax + 1e-12 >= kmax_dr01}"
        )
        print("\nWindow thresholds (um^-1) and counts:")
        thresholds = [
            ("DR05", 1.8),
            ("DR04d(adequate,minN8)", kmax_dr04d),
            ("DR03", 2.1),
            ("DR01(overlap)", kmax_dr01),
        ]
        for name, t in thresholds:
            n = sum(1 for k in ks if k <= float(t) + 1e-12)
            print(f"  {name}: k<= {float(t):.6g} -> N={n}")
        return 0

    # DS-02 pinned overlap requirement.
    if max(ks) + 1e-12 < kmax_dr01:
        raise RuntimeError(f"CSV max(k)={max(ks):g} does not reach required {kmax_dr01} um^-1")

    run_date = str(date.today())

    specs = [
        WindowSpec("DR05", 1.8),
        WindowSpec("DR04d", kmax_dr04d),
        WindowSpec("DR03", 2.1),
        WindowSpec("DR01", kmax_dr01),
    ]

    for spec in specs:
        out_linear = ds02_dir / f"{spec.window_id.lower()}_fit_artifact.json"
        out_curved = ds02_dir / f"{spec.window_id.lower()}_fit_artifact_curved.json"
        _run_generate(
            csv_path=csv_path,
            figure=figure,
            out_linear=out_linear,
            out_curved=out_curved,
            kmax_um_inv=float(spec.kmax_um_inv),
            window_id=str(spec.window_id),
            run_date=run_date,
            force=bool(args.force),
        )

    if not bool(args.no_update_fingerprint):
        csv_sha256 = _sha256_file(csv_path)
        _update_data_fingerprint_md(ds02_dir, csv_sha256=csv_sha256, rows=len(rows))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
