"""OV-SND-03N2: secondary-source multi-density conditions (computed lock).

Purpose
- Provide the governance-safe ingestion point for a *secondary* density source
  that includes multiple explicit density conditions (or sufficient parameters
  to compute them without interpretation drift).

Status discipline
- This record is expected to remain BLOCKED until:
  - a pinned PDF exists at formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf
  - a frozen multi-row density table exists (CSV + metadata)
  - explicit mapping keys are recorded in OV-BR-SND-02

Design constraints
- Deterministic, fingerprinted computed lock
- No density values are fabricated in-code
- No implied condition identity across sources
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
import re
from pathlib import Path
from typing import Any


def _require_pdfplumber():
    try:
        import pdfplumber  # type: ignore
    except ModuleNotFoundError as e:  # pragma: no cover
        raise RuntimeError(
            "pdfplumber is required only for PDF text extraction paths. "
            "Regen from frozen artifacts should not call this path; install pdfplumber into the active interpreter/venv "
            "only if you need to (re)extract from the pinned PDF."
        ) from e
    return pdfplumber


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _read_density_conditions_csv(csv_path: Path) -> tuple[list[dict[str, Any]], str]:
    """Return (rows, csv_sha256_of_text) after validating schema."""

    text = csv_path.read_text(encoding="utf-8")
    sha = _sha256_text(text)

    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        expected = ["density_condition_key", "n0_cm3", "source_locator", "notes"]
        if r.fieldnames != expected:
            raise ValueError(f"Unexpected columns: {r.fieldnames} (expected {expected})")
        out = []
        for row in r:
            out.append(
                {
                    "density_condition_key": str(row["density_condition_key"]),
                    "n0_cm3": float(row["n0_cm3"]),
                    "source_locator": str(row["source_locator"]),
                    "notes": str(row["notes"]),
                }
            )

    keys = [str(x["density_condition_key"]) for x in out]
    if len(keys) != len(set(keys)):
        raise ValueError("Duplicate density_condition_key in secondary density CSV")

    return out, sha


def _rows_preview(rows: list[dict[str, Any]], *, limit: int = 10) -> list[dict[str, Any]]:
    """Deterministic preview of density conditions.

    Governance intent: prevent silent reinterpretation by explicitly naming the
    condition keys and values in the computed lock. This remains bookkeeping-only.
    """

    out: list[dict[str, Any]] = []
    for r in rows[: int(limit)]:
        out.append(
            {
                "density_condition_key": str(r["density_condition_key"]),
                "n0_cm3": float(r["n0_cm3"]),
                "source_locator": str(r["source_locator"]),
            }
        )
    return out


def _normalize_extracted_text(s: str) -> str:
    return (
        s.replace("\u2212", "-")
        .replace("\u2013", "-")
        .replace("\u2014", "-")
        .replace("\u00d7", "x")
    )


def _split_two_panel_figure_by_row_whitespace(*, gray: list[list[float]]) -> int:
    """Return a deterministic split row between top and bottom panels.

    Uses a simple "minimum dark pixel count" heuristic in the middle band.
    """

    # Convert to boolean "very dark" for robustness.
    # gray is HxW floats.
    h = len(gray)
    w = len(gray[0]) if h else 0
    if h < 10 or w < 10:
        raise RuntimeError("Unexpected figure dimensions; cannot split panels")

    # Count very-dark pixels per row.
    row_counts = []
    for y in range(h):
        c = 0
        gy = gray[y]
        for x in range(w):
            if gy[x] < 80.0:
                c += 1
        row_counts.append(c)

    lo = int(h * 0.35)
    hi = int(h * 0.65)
    if hi <= lo + 5:
        raise RuntimeError("Invalid middle band for split detection")

    best_y = lo
    best = row_counts[lo]
    for y in range(lo, hi):
        if row_counts[y] < best:
            best = row_counts[y]
            best_y = y

    return int(best_y)


def _compute_grayscale_u8_from_rgb(rgb: "list[list[tuple[int,int,int]]]" | Any) -> list[list[float]]:
    """Compute grayscale luminance values as floats in [0,255].

    Accepts an array-like HxWx3 (e.g. numpy array) without requiring numpy.
    """

    if hasattr(rgb, "shape"):
        shp = getattr(rgb, "shape")
        h = int(shp[0])
        w = int(shp[1])
    else:
        h = int(len(rgb))
        w = int(len(rgb[0]))

    out: list[list[float]] = []
    for y in range(h):
        row: list[float] = []
        for x in range(w):
            px = rgb[y][x]
            r = float(px[0])
            g = float(px[1])
            b = float(px[2])
            row.append(0.2126 * r + 0.7152 * g + 0.0722 * b)
        out.append(row)
    return out


def _connected_components_4(mask: list[list[bool]]) -> list[dict[str, Any]]:
    """Return connected components with basic stats (4-neighbor).

    Each component dict contains: area, x0, x1, y0, y1, cx, cy.
    """

    h = len(mask)
    w = len(mask[0]) if h else 0
    vis = [[False] * w for _ in range(h)]
    comps: list[dict[str, Any]] = []

    for y in range(h):
        for x in range(w):
            if not mask[y][x] or vis[y][x]:
                continue
            stack = [(y, x)]
            vis[y][x] = True
            xs: list[int] = []
            ys: list[int] = []
            while stack:
                yy, xx = stack.pop()
                xs.append(xx)
                ys.append(yy)
                if yy > 0 and mask[yy - 1][xx] and not vis[yy - 1][xx]:
                    vis[yy - 1][xx] = True
                    stack.append((yy - 1, xx))
                if yy + 1 < h and mask[yy + 1][xx] and not vis[yy + 1][xx]:
                    vis[yy + 1][xx] = True
                    stack.append((yy + 1, xx))
                if xx > 0 and mask[yy][xx - 1] and not vis[yy][xx - 1]:
                    vis[yy][xx - 1] = True
                    stack.append((yy, xx - 1))
                if xx + 1 < w and mask[yy][xx + 1] and not vis[yy][xx + 1]:
                    vis[yy][xx + 1] = True
                    stack.append((yy, xx + 1))

            area = int(len(xs))
            x0 = int(min(xs))
            x1 = int(max(xs))
            y0 = int(min(ys))
            y1 = int(max(ys))
            cx = float(sum(xs)) / float(area)
            cy = float(sum(ys)) / float(area)
            comps.append({"area": area, "x0": x0, "x1": x1, "y0": y0, "y1": y1, "cx": cx, "cy": cy})

    return comps


def _digitize_secondary_density_conditions_from_pinned_figure(
    *, png_path: Path
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    r"""Digitize >=2 density conditions from a pinned two-panel PNG.

    Target
    - Panel (b): filled-circle series for chemical potential $\mu/k_B$ in $\mu K$.
    - Convert $\mu$ to central density via $n_0 = \mu / g$, with $g = 4\pi\hbar^2 a/m$.

    Governance
    - Deterministic connected-components digitizer
    - No smoothing, fitting, interpolation, or cross-regime inference
    - Uses only declared constants extracted from the pinned PDF text (species + scattering length)
    """

    # Local import to avoid forcing a hard dependency at module import time.
    from PIL import Image

    img = Image.open(png_path).convert("RGB")
    rgb = img.load()
    w, h = img.size

    # Build an RGB array-like interface (indexable by [y][x]).
    # PIL's pixel access is [x,y], so we wrap in a tiny adapter.
    class _RGB:
        shape = (h, w, 3)

        def __getitem__(self, y: int):
            return [rgb[x, y] for x in range(w)]

    gray = _compute_grayscale_u8_from_rgb(_RGB())

    split_y = _split_two_panel_figure_by_row_whitespace(gray=gray)
    # bottom panel coords are relative to split_y
    gray_b = gray[split_y:]
    hb = len(gray_b)
    wb = len(gray_b[0]) if hb else 0

    # Boolean masks for axis/label detection.
    very_dark_b = [[g < 80.0 for g in row] for row in gray_b]
    dark_b = [[g < 170.0 for g in row] for row in gray_b]

    # Axis detection: bottom axis is the densest dark row near the bottom.
    row_counts = [sum(1 for v in row if v) for row in very_dark_b]
    bottom_start = int(hb * 0.55)
    axis_y = int(max(range(bottom_start, hb), key=lambda yy: row_counts[yy]))

    # Y-axis detection: choose column with the longest contiguous run of very-dark pixels near the left.
    left_lim = int(wb * 0.40)
    best_x = 0
    best_run = -1
    for x in range(0, left_lim):
        run = 0
        mx = 0
        for y in range(hb):
            if very_dark_b[y][x]:
                run += 1
                mx = max(mx, run)
            else:
                run = 0
        if mx > best_run:
            best_run = mx
            best_x = x
    axis_x = int(best_x)

    # Locate y-axis tick labels by connected components in a narrow strip near the axis.
    x_lo = max(0, axis_x - 65)
    x_hi = max(0, axis_x - 5)
    strip = [row[x_lo:x_hi] for row in dark_b[:axis_y]]
    comps = _connected_components_4(strip)

    # Keep plausible digit blobs.
    digit_blobs = []
    for c in comps:
        area = int(c["area"])
        hbb = int(c["y1"] - c["y0"] + 1)
        wbb = int(c["x1"] - c["x0"] + 1)
        if area < 12 or area > 2500:
            continue
        if hbb < 6 or wbb < 3:
            continue
        digit_blobs.append(c)

    # Group blobs into label lines by y proximity.
    digit_blobs.sort(key=lambda d: float(d["cy"]))
    lines: list[dict[str, Any]] = []
    for b in digit_blobs:
        cy = float(b["cy"])
        placed = False
        for ln in lines:
            if abs(cy - float(ln["cy"])) <= 8.0:
                ln["y0"] = int(min(int(ln["y0"]), int(b["y0"])))
                ln["y1"] = int(max(int(ln["y1"]), int(b["y1"])))
                ln["cy"] = (float(ln["y0"]) + float(ln["y1"])) / 2.0
                ln["area"] = int(ln["area"]) + int(b["area"])
                placed = True
                break
        if not placed:
            lines.append(
                {
                    "y0": int(b["y0"]),
                    "y1": int(b["y1"]),
                    "cy": float(b["cy"]),
                    "area": int(b["area"]),
                }
            )

    lines.sort(key=lambda d: float(d["cy"]))

    # Keep the four strongest candidate label lines.
    cand = [ln for ln in lines if int(ln["area"]) >= 80]
    if len(cand) < 4:
        raise RuntimeError("Could not locate 4 y-axis tick-label lines for panel (b)")

    # Choose four by y (top->bottom), targeting y-axis labels: 1.5, 1.0, 0.5, 0.0.
    cand.sort(key=lambda d: float(d["cy"]))
    # Take top, two middles, bottom (by quantiles) to remain stable if an extra line appears.
    ys = [float(c["cy"]) for c in cand]
    ys_sorted = sorted(ys)
    targets = [ys_sorted[0], ys_sorted[len(ys_sorted) // 3], ys_sorted[(2 * len(ys_sorted)) // 3], ys_sorted[-1]]
    selected: list[dict[str, Any]] = []
    for t in targets:
        best = min(cand, key=lambda c: abs(float(c["cy"]) - float(t)))
        if all(abs(float(best["cy"]) - float(s["cy"])) > 5.0 for s in selected):
            selected.append(best)
    selected.sort(key=lambda d: float(d["cy"]))
    if len(selected) != 4:
        raise RuntimeError("Could not deterministically select 4 y-axis tick-label lines")

    # Map the label-line y positions to their intended values.
    # IMPORTANT: these are ordered by y (top->bottom) in the figure.
    y_for_val = {
        1.5: float(selected[0]["cy"]),
        1.0: float(selected[1]["cy"]),
        0.5: float(selected[2]["cy"]),
        0.0: float(selected[3]["cy"]),
    }

    # Marker detection in plot region.
    px1 = int(axis_x + 8)
    py1 = 10
    px2 = int(wb - 10)
    py2 = int(axis_y - 8)
    if px2 <= px1 + 10 or py2 <= py1 + 10:
        raise RuntimeError("Invalid plot window for panel (b)")

    plot_dark = [[gray_b[y][x] < 180.0 for x in range(px1, px2)] for y in range(py1, py2)]
    hp = len(plot_dark)
    wp = len(plot_dark[0]) if hp else 0

    # Remove the vertical dashed line by detecting a high-coverage column.
    col_counts = [0] * wp
    for y in range(hp):
        row = plot_dark[y]
        for x in range(wp):
            if row[x]:
                col_counts[x] += 1
    dashed_cols = [i for i, c in enumerate(col_counts) if c > int(0.70 * hp)]
    dashed_x: int | None = None
    if dashed_cols:
        dashed_x = int(sorted(dashed_cols)[len(dashed_cols) // 2])

    comps_plot = _connected_components_4(plot_dark)
    blobs: list[dict[str, Any]] = []
    for c in comps_plot:
        area = int(c["area"])
        wbb = int(c["x1"] - c["x0"] + 1)
        hbb = int(c["y1"] - c["y0"] + 1)
        if area < 6 or area > 800:
            continue
        if wbb < 3 or hbb < 3 or wbb > 30 or hbb > 30:
            continue
        aspect = max(float(wbb) / float(hbb), float(hbb) / float(wbb))
        if aspect > 2.5:
            continue
        cx = float(c["cx"])
        cy = float(c["cy"])
        if cx < 5.0 or cy > float(hp - 5):
            continue
        if dashed_x is not None and abs(cx - float(dashed_x)) < 10.0 and wbb <= 6:
            continue
        blobs.append(c)

    # Classify filled-circle points (μ series) vs open circles / text.
    mu_points: list[dict[str, Any]] = []
    for b in blobs:
        cx = int(round(float(b["cx"])))
        cy = int(round(float(b["cy"])))
        # center pixel in the plot window
        g_center = float(gray_b[py1 + cy][px1 + cx])
        if g_center >= 90.0:
            continue
        # compute μ/kB from y scaling
        y15 = float(y_for_val[1.5]) - float(py1)
        y00 = float(y_for_val[0.0]) - float(py1)
        mu_uK = 1.5 * ((y00 - float(b["cy"])) / (y00 - y15))
        # µ-series values are in the low band (as also stated in the pinned PDF text).
        if not (0.05 <= mu_uK <= 0.6):
            continue
        mu_points.append(
            {
                "px": int(px1 + cx),
                "py": int(py1 + cy),
                "mu_over_kb_uK": float(mu_uK),
                "raw_blob": {"area": int(b["area"]), "w": int(b["x1"] - b["x0"] + 1), "h": int(b["y1"] - b["y0"] + 1)},
            }
        )

    mu_points.sort(key=lambda d: int(d["px"]))

    if len(mu_points) < 2:
        raise RuntimeError("Insufficient μ points detected in panel (b) (need>=2)")

    # Physics constants (deterministic; no fitting).
    # Sodium-23 mass.
    m_u = 1.66053906660e-27
    m = 22.98976928 * m_u
    # Scattering length a=2.75 nm (as extractable in the pinned PDF text snapshot).
    a = 2.75e-9
    hbar = 1.054571817e-34
    kB = 1.380649e-23
    g = 4.0 * 3.141592653589793 * (hbar**2) * a / m

    rows: list[dict[str, Any]] = []
    for i, p in enumerate(mu_points, start=1):
        mu_over_kb_uK = float(p["mu_over_kb_uK"])
        mu_J = kB * (mu_over_kb_uK * 1.0e-6)
        n0_m3 = mu_J / g
        n0_cm3 = float(n0_m3 * 1.0e-6)
        rows.append(
            {
                "density_condition_key": f"sk98_mu_digitized_{i:02d}",
                "n0_cm3": float(n0_cm3),
                "source_locator": (
                    f"png_digitization:{png_path.as_posix()}::panel_b_mu:"
                    f"px={int(p['px'])},py={int(p['py'])},mu_over_kb_uK={mu_over_kb_uK:.6g}"
                ),
                "notes": "Derived from digitized μ/k_B (μK) in panel (b); n0=μ/g with a=2.75nm (Na-23).",
            }
        )

    report = {
        "method": "png_connected_components_digitization",
        "png_relpath": str(png_path.as_posix()),
        "png_sha256": _sha256_file(png_path),
        "figure": {
            "split_y": int(split_y),
            "axis_x": int(axis_x),
            "axis_y": int(axis_y),
            "y_for_val_mu_over_kb_uK": {str(k): float(v) for k, v in y_for_val.items()},
        },
        "mu_points": list(mu_points),
        "constants": {
            "species": "Na-23",
            "a_m": float(a),
            "m_kg": float(m),
            "g_J_m3": float(g),
        },
        "notes": "Digitizes low-μ filled-circle series only (0.05<=μ/kB<=0.6 μK).",
    }

    return rows, report


def _extract_density_conditions_from_pdf(*, pdf_path: Path) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Deterministically extract explicit density conditions from pinned PDF text.

    Current behavior
    - Extracts only *explicitly* stated densities in cm^-3.
    - Does not digitize plots or compute densities from derived quantities.

    This keeps the record governance-safe and avoids interpretation drift.
    """

    pdfplumber = _require_pdfplumber()
    with pdfplumber.open(str(pdf_path)) as pdf:
        page_texts = [_normalize_extracted_text(pg.extract_text() or "") for pg in pdf.pages]

    full = "\n".join(page_texts)

    # Pinned explicit match observed in the uploaded cond-mat/9801262 PDF:
    # "n = 3.8x1014cm-3" (pdf text extraction collapses 10^14 -> 1014).
    pat = re.compile(r"\bn\s*=\s*3\.8\s*x\s*1014\s*cm\s*-\s*3\b", flags=re.IGNORECASE)
    matches = list(pat.finditer(full))

    rows: list[dict[str, Any]] = []
    match_details: list[dict[str, Any]] = []

    if len(matches) >= 1:
        # Locate a deterministic page for reporting.
        page_number: int | None = None
        for i, t in enumerate(page_texts, start=1):
            if pat.search(t) is not None:
                page_number = int(i)
                break

        rows.append(
            {
                "density_condition_key": "sk98_max_density_example",
                "n0_cm3": float(3.8e14),
                "source_locator": f"pdf_text_match:page{page_number or 'unknown'}:n=3.8x10^14cm^-3",
                "notes": "Extracted as explicit text; PDF extraction collapses 10^14 to 1014 in this snapshot.",
            }
        )

        match_details.append(
            {
                "pattern": "n = 3.8x1014cm-3 (interpreted as 3.8e14 cm^-3)",
                "match_count": int(len(matches)),
                "page_number": int(page_number) if page_number is not None else None,
            }
        )

    extraction_report = {
        "method": "pdfplumber_text_regex",
        "pdf_page_count": int(len(page_texts)),
        "patterns": match_details,
        "notes": "This extractor only ingests explicit density statements; additional density conditions may require table/figure digitization as a separate governed step.",
    }

    return rows, extraction_report


def _render_density_conditions_csv_text(rows: list[dict[str, Any]]) -> str:
    header = ["density_condition_key", "n0_cm3", "source_locator", "notes"]
    lines = [",".join(header)]
    for r in rows:
        # Comma-safe minimal quoting (deterministic): replace internal newlines.
        def q(s: str) -> str:
            s = str(s).replace("\r", " ").replace("\n", " ")
            if "," in s or '"' in s:
                s = s.replace('"', '""')
                return f'"{s}"'
            return s

        lines.append(
            ",".join(
                [
                    q(str(r["density_condition_key"])),
                    ("%.12g" % float(r["n0_cm3"])),
                    q(str(r["source_locator"])),
                    q(str(r["notes"])),
                ]
            )
        )
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class OVSND03N2SecondaryDensityConditionsDigitizedRecord:
    schema: str
    date: str

    observable_id: str

    status: dict[str, Any]
    source: dict[str, Any]
    dataset: dict[str, Any] | None
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "source": dict(self.source),
            "dataset": None if self.dataset is None else dict(self.dataset),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd03n2_secondary_density_conditions_digitized_record(
    *,
    date: str = "2026-01-24",
) -> OVSND03N2SecondaryDensityConditionsDigitizedRecord:
    repo_root = _find_repo_root(Path(__file__))

    # Expected pinning locations.
    pdf_rel = "formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf"
    meta_rel = "formal/external_evidence/bec_sound_density_secondary_TBD/source.metadata.json"
    csv_rel = (
        "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/"
        "density_conditions.csv"
    )
    csv_meta_rel = (
        "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/"
        "density_conditions.metadata.json"
    )

    pdf_path = repo_root / pdf_rel
    meta_path = repo_root / meta_rel
    csv_path = repo_root / csv_rel
    csv_meta_path = repo_root / csv_meta_rel

    blockers: list[str] = []
    pdf_sha256: str | None = None
    if not pdf_path.exists():
        blockers.append("secondary_pdf_not_pinned")
    else:
        pdf_sha256 = _sha256_file(pdf_path)

    if not meta_path.exists():
        blockers.append("secondary_pdf_metadata_missing")

    dataset: dict[str, Any] | None = None
    if not csv_path.exists():
        blockers.append("secondary_density_conditions_csv_missing")
    if not csv_meta_path.exists():
        blockers.append("secondary_density_conditions_metadata_missing")

    if csv_path.exists():
        rows, csv_sha = _read_density_conditions_csv(csv_path)
        dataset = {
            "csv_relpath": csv_rel,
            "metadata_relpath": csv_meta_rel,
            "row_count": int(len(rows)),
            "rows_preview": _rows_preview(rows, limit=10),
            "columns": [
                {"name": "density_condition_key", "unit": "(label)", "dtype": "string"},
                {"name": "n0_cm3", "unit": "cm^-3", "dtype": "float"},
                {"name": "source_locator", "unit": "(locator)", "dtype": "string"},
                {"name": "notes", "unit": "(text)", "dtype": "string"},
            ],
            "csv_sha256": str(csv_sha),
        }
        if int(len(rows)) < 2:
            blockers.append("insufficient_density_conditions_for_constancy (need>=2)")

    status = {
        "blocked": bool(len(blockers) > 0),
        "blockers": list(blockers),
    }

    source = {
        "secondary_pdf_relpath": pdf_rel,
        "secondary_pdf_sha256": pdf_sha256,
        "secondary_pdf_metadata_relpath": meta_rel,
        "notes": (
            "This is the governance-safe ingestion point for a secondary multi-density source. "
            "It does not fabricate density values; it remains blocked until a pinned PDF and a frozen multi-row table exist."
        ),
    }

    scope_limits = [
        "bookkeeping_only",
        "no_physics_claim",
        "no_condition_identity_assumption",
        "no_imputation",
        "no_continuity_claim",
        "non_decisive_by_design",
    ]

    return OVSND03N2SecondaryDensityConditionsDigitizedRecord(
        schema="OV-SND-03N2_secondary_density_conditions_digitized/v1",
        date=str(date),
        observable_id="OV-SND-03N2",
        status=status,
        source=source,
        dataset=dataset,
        scope_limits=scope_limits,
    )


def _validate_frozen_density_conditions_artifacts(*, csv_path: Path, meta_path: Path) -> None:
    """Validate frozen CSV + metadata consistency.

    This is intentionally lightweight and does not require the pinned PDF/PNG.
    """

    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    csv_text = csv_path.read_text(encoding="utf-8")

    expected_sha = str(meta.get("dataset", {}).get("csv_sha256") or "")
    if not expected_sha:
        raise RuntimeError("OV-SND-03N2 metadata missing dataset.csv_sha256")
    if _sha256_text(csv_text) != expected_sha:
        raise RuntimeError("OV-SND-03N2 frozen CSV sha256 does not match metadata")

    reader = csv.DictReader(csv_text.splitlines())
    expected_cols = ["density_condition_key", "n0_cm3", "source_locator", "notes"]
    if reader.fieldnames != expected_cols:
        raise RuntimeError(f"OV-SND-03N2 CSV has unexpected columns: {reader.fieldnames}")
    rows = list(reader)

    expected_row_count = meta.get("dataset", {}).get("row_count")
    if isinstance(expected_row_count, int) and len(rows) != expected_row_count:
        raise RuntimeError("OV-SND-03N2 CSV row_count does not match metadata")


def write_ovsnd03n2_digitized_artifacts(
    *,
    date: str = "2026-01-24",
    force_redigitize: bool = False,
) -> dict[str, Path]:
    """Write frozen CSV + metadata under the secondary evidence folder.

    Default behavior is governance-safe and fast:
    - If frozen CSV+metadata already exist and validate, reuse them (no digitization).
    - Only if missing (or force_redigitize=True) will this function run extraction/digitization.
    """

    repo_root = _find_repo_root(Path(__file__))

    csv_rel = (
        "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/"
        "density_conditions.csv"
    )
    meta_rel = (
        "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/"
        "density_conditions.metadata.json"
    )

    csv_path = repo_root / csv_rel
    meta_path = repo_root / meta_rel

    if (not force_redigitize) and csv_path.exists() and meta_path.exists():
        _validate_frozen_density_conditions_artifacts(csv_path=csv_path, meta_path=meta_path)
        return {"csv": csv_path, "metadata": meta_path}

    pdf_rel = "formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf"
    pdf_path = repo_root / pdf_rel
    if not pdf_path.exists():
        raise FileNotFoundError(f"Missing pinned secondary PDF: {pdf_path}")

    # Prefer deterministic figure digitization when the pinned PNG exists; fall back to explicit-text regex.
    png_rel = "formal/external_evidence/bec_sound_density_secondary_TBD/Screenshot 2026-01-24 153305.png"
    png_path = repo_root / png_rel
    if png_path.exists():
        rows, report = _digitize_secondary_density_conditions_from_pinned_figure(png_path=png_path)
    else:
        rows, report = _extract_density_conditions_from_pdf(pdf_path=pdf_path)
    csv_text = _render_density_conditions_csv_text(rows)
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.parent.mkdir(parents=True, exist_ok=True)

    csv_path.write_text(csv_text, encoding="utf-8", newline="\n")

    rec = ovsnd03n2_secondary_density_conditions_digitized_record(date=str(date))
    payload = {
        "schema": "OV-SND-03N2_density_conditions_metadata/v1",
        "date": str(date),
        "observable_id": rec.observable_id,
        "source": {
            "secondary_pdf_relpath": pdf_rel,
            "secondary_pdf_sha256": _sha256_file(pdf_path),
            "secondary_png_relpath": png_rel if png_path.exists() else None,
            "secondary_png_sha256": _sha256_file(png_path) if png_path.exists() else None,
        },
        "extraction": report,
        "dataset": {
            "csv_relpath": csv_rel,
            "row_count": int(len(rows)),
            "csv_sha256": _sha256_text(csv_text),
        },
        "record_fingerprint": rec.fingerprint(),
        "scope_limits": rec.scope_limits,
    }
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {"csv": csv_path, "metadata": meta_path}


def render_ovsnd03n2_lock_markdown(record: OVSND03N2SecondaryDensityConditionsDigitizedRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-03N2 — Secondary-source multi-density conditions (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping only; no physics claim\n"
        "- Remains blocked until a pinned secondary PDF + frozen multi-row density table exist\n"
        "- No implied condition identity across sources\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd03n2_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-03N2_secondary_density_conditions_digitized.md"

    rec = ovsnd03n2_secondary_density_conditions_digitized_record(date=str(date))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd03n2_lock_markdown(rec), encoding="utf-8")
    return out
