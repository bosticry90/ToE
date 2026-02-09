"""Convert a WebPlotDigitizer (WPD) export into the DS-02 omega_k_data.csv schema.

Why this exists
- Shammass 2012 Fig. 2 has no numeric table; DS-02 must be digitized.
- WPD typically exports a 2-column CSV (x,y). This tool wraps that into the
  repository's DS-02 schema and applies canonical ordering.

Expected WPD input
- CSV with headers like: X,Y   (common)
- or no headers (two numeric columns)
- X interpreted as k in um^-1
- Y interpreted as omega/2pi in kHz

Output
- Writes/overwrites DS-02 omega_k_data.csv (or a specified output path)
- Columns: source,figure,k_um_inv,omega_over_2pi_kHz,sigma_k_um_inv,sigma_omega_over_2pi_kHz,notes

Usage
  python -m formal.python.tools.convert_webplotdigitizer_to_ds02_csv \
    --in wpd_export.csv \
    --out formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv \
    --source "Shammass2012_arXiv1207.3440v2_Fig2_filled_circles" \
    --figure "Fig. 2" \
    --notes "filled circles; centroid picks; error bars not digitized"

Then run
  python -m formal.python.tools.generate_ds02_dr_artifacts --report
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
import sys
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


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _parse_two_col_csv(path: Path) -> list[tuple[float, float]]:
    text = path.read_text(encoding="utf-8")
    # Heuristic: if the first line has non-numeric tokens, treat as header.
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    if not lines:
        raise RuntimeError(f"Empty input CSV: {path}")

    # Try DictReader first (handles headers like X,Y)
    try:
        with path.open("r", encoding="utf-8", newline="") as f:
            reader = csv.DictReader(f)
            if reader.fieldnames is None:
                raise RuntimeError("No fieldnames")

            # Accept common header spellings.
            fields = [fn.strip() for fn in reader.fieldnames]
            lower = [fn.lower() for fn in fields]
            if "x" in lower and "y" in lower:
                x_key = fields[lower.index("x")]
                y_key = fields[lower.index("y")]
            elif "k" in lower and ("omega" in lower or "w" in lower):
                x_key = fields[lower.index("k")]
                y_key = fields[lower.index("omega") if "omega" in lower else lower.index("w")]
            else:
                # Fall back to first two columns.
                x_key, y_key = fields[0], fields[1]

            out: list[tuple[float, float]] = []
            for r in reader:
                if not r:
                    continue
                x = str(r.get(x_key, "")).strip()
                y = str(r.get(y_key, "")).strip()
                if x == "" or y == "":
                    continue
                out.append((float(x), float(y)))
            if out:
                return out
    except Exception:
        pass

    # Fallback: plain two-column CSV with no header.
    out2: list[tuple[float, float]] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader2 = csv.reader(f)
        for row in reader2:
            if not row:
                continue
            if len(row) < 2:
                continue
            a = str(row[0]).strip()
            b = str(row[1]).strip()
            if a == "" or b == "":
                continue
            # Skip obvious header-like first row.
            try:
                out2.append((float(a), float(b)))
            except Exception:
                continue
    if not out2:
        raise RuntimeError(f"Could not parse two numeric columns from {path}")
    return out2


def _write_ds02_csv(
    *,
    out_path: Path,
    points: list[tuple[float, float]],
    source: str,
    figure: str,
    notes: str,
) -> None:
    rows = [
        {
            "source": source,
            "figure": figure,
            "k_um_inv": f"{k:.12g}",
            "omega_over_2pi_kHz": f"{w:.12g}",
            "sigma_k_um_inv": "",
            "sigma_omega_over_2pi_kHz": "",
            "notes": notes,
        }
        for (k, w) in points
    ]

    # Canonical ordering.
    rows.sort(key=lambda r: float(r["k_um_inv"]))

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "source",
                "figure",
                "k_um_inv",
                "omega_over_2pi_kHz",
                "sigma_k_um_inv",
                "sigma_omega_over_2pi_kHz",
                "notes",
            ],
        )
        writer.writeheader()
        for r in rows:
            writer.writerow(r)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--in", dest="in_path", required=True, help="Input CSV from WebPlotDigitizer")
    parser.add_argument(
        "--out",
        dest="out_path",
        default=None,
        help="Output DS-02 omega_k_data.csv path (default: pinned DS-02 packet)",
    )
    parser.add_argument(
        "--source",
        default="Shammass2012_arXiv1207.3440v2_Fig2_filled_circles",
        help="Value to stamp into DS-02 'source' column",
    )
    parser.add_argument("--figure", default="Fig. 2", help="Value to stamp into DS-02 'figure' column")
    parser.add_argument(
        "--notes",
        default="filled circles; centroid picks; error bars not digitized",
        help="Value to stamp into DS-02 'notes' column",
    )

    args = parser.parse_args(argv)

    repo_root = _find_repo_root(Path(__file__))
    default_out = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_bragg_ds02_lowk_dataset_TBD"
        / "omega_k_data.csv"
    )

    in_path = Path(args.in_path)
    out_path = Path(args.out_path) if args.out_path is not None else default_out

    pts = _parse_two_col_csv(in_path)
    if len(pts) < 2:
        raise RuntimeError("Need at least 2 points")

    _write_ds02_csv(
        out_path=out_path,
        points=pts,
        source=str(args.source),
        figure=str(args.figure),
        notes=str(args.notes),
    )

    print(f"Wrote DS-02 CSV: {out_path} (N={len(pts)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
