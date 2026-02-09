"""Generate B1 (Ernst 2009 Fig2a) DR window artifacts from the pinned digitization CSV.

This is a thin wrapper around `formal.python.tools.generate_external_dr_artifacts`.

Outputs (written into the B1 evidence folder):
- dr01_fit_artifact.json + dr01_fit_artifact_curved.json
- dr03_fit_artifact.json + dr03_fit_artifact_curved.json
- dr04d_fit_artifact.json + dr04d_fit_artifact_curved.json
- dr05_fit_artifact.json + dr05_fit_artifact_curved.json

Window policy (B1 specific)
- DR04d: smallest kmax that yields N>=5 points (minN5)
- DR03: fixed kmax at 7.30071 um^-1 (existing canonical window)
- DR01: largest kmax <= 8.28312 um^-1 that yields a DQ-01_v1 PASS (tighten to clear borderline rmse)
- DR05: smallest kmax >= 6.53811 um^-1 that yields a DQ-01_v1 PASS and differs from DR03 when possible

Notes
- This script does not digitize the PDF; it consumes omega_k_data.csv.
- Units: omega_over_2pi_kHz is treated as kHz for B1 (omega = 2*pi*f).

Usage
  python -m formal.python.tools.generate_b1_dr_artifacts --force
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


def _load_rows(csv_path: Path, *, figure: str | None) -> list[dict[str, str]]:
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        rows = list(csv.DictReader(f))

    if figure is not None:
        rows = [r for r in rows if (r.get("figure", "").strip() == str(figure))]

    if not rows:
        raise RuntimeError(f"No rows found in {csv_path} for figure={figure!r}")

    rows.sort(key=lambda r: float(r["k_um_inv"]))
    return rows


def _sample_kw_for_kmax_khz(rows: list[dict[str, str]], *, kmax_um_inv: float) -> tuple[tuple[float, float], ...]:
    items: list[tuple[float, float]] = []
    for r in rows:
        k_um = float(r["k_um_inv"])
        if k_um <= float(kmax_um_inv) + 1e-12:
            f_khz = float(r["omega_over_2pi_kHz"])
            k_m_inv = k_um * 1.0e6
            omega_rad_s = 2.0 * math.pi * (f_khz * 1.0e3)
            items.append((k_m_inv, omega_rad_s))

    items.sort(key=lambda t: (t[0], t[1]))
    return tuple(items)


def _dq01_passes_at_kmax(rows: list[dict[str, str]], *, kmax_um_inv: float) -> bool:
    sample_kw = _sample_kw_for_kmax_khz(rows, kmax_um_inv=float(kmax_um_inv))
    if len(sample_kw) < 3:
        return False

    fit = dr01_fit_curved_from_sample_kw(
        sample_kw,
        u_fixed=0.0,
        tag="B1_window_probe",
        source_kind="csv",
        source_ref="B1 omega_k_data.csv",
        fit_method_tag="window probe",
    )
    adequacy = dr01_check_curved_fit_adequacy(fit, policy="DQ-01_v1")
    return bool(adequacy.passes)


def _compute_minN5_kmax(ks: list[float]) -> float:
    if len(ks) < 5:
        raise RuntimeError("Need at least 5 points to compute minN5 window")
    return float(sorted(ks)[4])


def _format_kmax_for_tag(kmax_um_inv: float) -> str:
    k = (f"{kmax_um_inv:.6f}").rstrip("0").rstrip(".")
    return k.replace(".", "p")


def _tag(window_id: str, *, kmax_um_inv: float) -> str:
    return f"{window_id}_Ernst2009_Fig2a_kmax_{_format_kmax_for_tag(kmax_um_inv)}"


def _render_source_ref(*, csv_path: Path, figure: str | None, kmax_um_inv: float) -> str:
    fig = figure or "(unfiltered)"
    return (
        "Ernst et al. (2009) arXiv:0908.4242v1; "
        f"{fig}; "
        f"{csv_path.as_posix()}; "
        f"window k<= {kmax_um_inv:g} um^-1; "
        "omega=2*pi*f (f in kHz)"
    )


def _run_generate(
    *,
    csv_path: Path,
    figure: str | None,
    out_linear: Path,
    out_curved: Path,
    kmax_um_inv: float,
    window_id: str,
    force: bool,
) -> None:
    src_ref = _render_source_ref(csv_path=csv_path, figure=figure, kmax_um_inv=kmax_um_inv)
    tag = _tag(window_id, kmax_um_inv=kmax_um_inv)
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
        tag,
        "--tag-curved",
        tag + "_curved",
        "--source-ref",
        src_ref,
        "--fit-method-tag",
        f"Fig2a window k<= {kmax_um_inv:g} um^-1; u fixed to 0",
        "--fit-method-tag-curved",
        f"Fig2a curved omega/k = c0 + beta*k^2 on k<= {kmax_um_inv:g} um^-1; u fixed to 0",
        "--omega-over-2pi-units",
        "kHz",
    ]
    if figure is not None:
        argv.extend(["--figure", str(figure)])
    if force:
        argv.append("--force")

    generate_external_dr_artifacts.main(argv)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--csv",
        default=None,
        help="Path to B1 omega_k_data.csv (default: pinned B1 folder)",
    )
    parser.add_argument(
        "--figure",
        default="Fig2a",
        help="Filter by figure value in CSV (default: 'Fig2a'; set '' to disable)",
    )
    parser.add_argument("--report", action="store_true", help="Print dataset/window summary and exit")
    parser.add_argument("--force", action="store_true", help="Overwrite existing artifact files")
    args = parser.parse_args(argv)

    repo_root = _find_repo_root(Path(__file__))
    b1_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD"
    default_csv = b1_dir / "omega_k_data.csv"

    csv_path = Path(args.csv) if args.csv is not None else default_csv
    if not csv_path.exists():
        raise RuntimeError(f"CSV not found: {csv_path}")

    figure: str | None
    if args.figure is None or str(args.figure).strip() == "":
        figure = None
    else:
        figure = str(args.figure).strip()

    rows = _load_rows(csv_path, figure=figure)
    ks = [float(r["k_um_inv"]) for r in rows]
    ks_sorted = sorted(ks)

    # Canonical baselines (prior pinned windows)
    kmax_dr01_cap = 8.28312
    kmax_dr03 = 7.30071
    kmax_dr05_floor = 6.53811

    kmax_dr04d = _compute_minN5_kmax(ks_sorted)

    # DR01: tighten until DQ-01 passes.
    dr01_candidates = [k for k in ks_sorted if k <= kmax_dr01_cap + 1e-12]
    dr01_pass = [k for k in dr01_candidates if _dq01_passes_at_kmax(rows, kmax_um_inv=float(k))]
    if not dr01_pass:
        raise RuntimeError("No DR01 candidate kmax <= cap yields DQ-01 pass")
    kmax_dr01 = float(max(dr01_pass))

    # DR05: increase until DQ-01 passes; avoid duplicating DR03 if possible.
    dr05_candidates = [k for k in ks_sorted if k >= kmax_dr05_floor - 1e-12]
    dr05_pass = [k for k in dr05_candidates if _dq01_passes_at_kmax(rows, kmax_um_inv=float(k))]
    if not dr05_pass:
        raise RuntimeError("No DR05 candidate kmax >= floor yields DQ-01 pass")

    kmax_dr05 = None
    for k in sorted(dr05_pass):
        if abs(float(k) - float(kmax_dr03)) > 1e-12:
            kmax_dr05 = float(k)
            break
    if kmax_dr05 is None:
        kmax_dr05 = float(min(dr05_pass))

    if bool(args.report):
        kmin = min(ks_sorted)
        kmax = max(ks_sorted)
        print(f"B1 rows: N={len(rows)} (figure={figure!r})")
        print(f"k range (um^-1): [{kmin:.6g}, {kmax:.6g}]")
        print(f"CSV sha256: {_sha256_file(csv_path)}")
        print("\nWindow thresholds (um^-1) and counts:")
        thresholds = [
            ("DR04d(minN5)", kmax_dr04d),
            ("DR05(adequate)", kmax_dr05),
            ("DR03(fixed)", kmax_dr03),
            ("DR01(adequate,<=cap)", kmax_dr01),
        ]
        for name, t in thresholds:
            n = sum(1 for k in ks_sorted if k <= float(t) + 1e-12)
            print(f"  {name}: k<= {float(t):.6g} -> N={n}")
        return 0

    specs = [
        WindowSpec("DR04d", kmax_dr04d),
        WindowSpec("DR05", kmax_dr05),
        WindowSpec("DR03", kmax_dr03),
        WindowSpec("DR01", kmax_dr01),
    ]

    for spec in specs:
        out_linear = b1_dir / f"{spec.window_id.lower()}_fit_artifact.json"
        out_curved = b1_dir / f"{spec.window_id.lower()}_fit_artifact_curved.json"
        _run_generate(
            csv_path=csv_path,
            figure=figure,
            out_linear=out_linear,
            out_curved=out_curved,
            kmax_um_inv=float(spec.kmax_um_inv),
            window_id=str(spec.window_id),
            force=bool(args.force),
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
