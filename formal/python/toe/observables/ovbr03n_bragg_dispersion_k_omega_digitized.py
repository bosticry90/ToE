"""OV-BR-03N: digitized Bragg dispersion ω(k) under two explicit conditions (computed lock).

Digitization target
- Source PDF: Shammass et al. arXiv:1207.3440v2
- Figure: Fig. 2
- Render: `formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png` (zoom=4)
- Conditions (as declared in `dispersion_conditions.md`):
  - condition_A: filled circles
  - condition_B: open circles

Design constraints
- Deterministic (no RNG).
- Frozen artifacts: write condition CSVs + metadata JSON under external evidence.
- No PDF text-layer reliance (axis labels/ticks are rasterized).

Notes
- Axis ranges are read from the figure itself and encoded as explicit constants:
  - x: k [um^-1] over [0, 4.5]
  - y: ω/2π [kHz] over [0, 2.0]
- We use deterministic image heuristics to locate the plot box and extract marker
  centroids, then apply an affine pixel→data mapping.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np
from PIL import Image
from scipy import ndimage


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


@dataclass(frozen=True)
class PlotBox:
    left: int
    right: int
    top: int
    bottom: int

    def width(self) -> int:
        return int(self.right - self.left)

    def height(self) -> int:
        return int(self.bottom - self.top)


def _to_gray(img: np.ndarray) -> np.ndarray:
    if img.ndim != 3 or img.shape[2] != 3:
        raise ValueError("expected RGB image")
    r = img[:, :, 0].astype(np.float32)
    g = img[:, :, 1].astype(np.float32)
    b = img[:, :, 2].astype(np.float32)
    return (0.2126 * r + 0.7152 * g + 0.0722 * b).astype(np.float32)


def _find_plot_box(gray: np.ndarray, *, dark_threshold: int = 80) -> PlotBox:
    """Heuristically locate the main plot axes box.

    We look for a dense horizontal axis line near the bottom and a dense vertical
    axis line near the left. Then estimate plot extents from those lines.

    This mirrors the DS-02 PNG digitizer approach.
    """

    H, W = gray.shape
    dark = gray < float(dark_threshold)

    # Candidate x-axis: strongest horizontal dark density in the lower 40%.
    y0 = int(0.55 * H)
    row_scores = dark[y0:, :].mean(axis=1)
    y_axis = int(y0 + int(np.argmax(row_scores)))

    # Candidate y-axis: strongest vertical dark density in the left 40%.
    x1 = int(0.45 * W)
    col_scores = dark[:, :x1].mean(axis=0)
    x_axis = int(np.argmax(col_scores))

    row = dark[y_axis, :]
    xs = np.where(row)[0]
    if xs.size == 0:
        raise RuntimeError("Could not detect x-axis line")
    right = int(np.percentile(xs, 99.0))

    col = dark[:, x_axis]
    ys = np.where(col)[0]
    if ys.size == 0:
        raise RuntimeError("Could not detect y-axis line")
    top = int(np.percentile(ys, 1.0))

    left = int(x_axis + 1)
    bottom = int(y_axis - 1)

    pad_x = max(2, int(0.008 * W))
    pad_y = max(2, int(0.01 * H))

    left = min(max(left + pad_x, 0), W - 2)
    right = min(max(right - pad_x, left + 2), W - 1)
    top = min(max(top + pad_y, 0), bottom - 2)
    bottom = min(max(bottom - pad_y, top + 2), H - 1)

    if (right - left) < 100 or (bottom - top) < 100:
        raise RuntimeError(f"Detected plot box too small: left={left} right={right} top={top} bottom={bottom}")

    return PlotBox(left=left, right=right, top=top, bottom=bottom)


def _has_enclosed_hole(comp: np.ndarray) -> bool:
    if comp.ndim != 2:
        raise ValueError("comp must be 2D")

    h, w = comp.shape
    if h < 3 or w < 3:
        return False

    background = ~comp
    seeds = np.zeros_like(background, dtype=bool)
    seeds[0, :] = True
    seeds[-1, :] = True
    seeds[:, 0] = True
    seeds[:, -1] = True
    seeds &= background

    reachable = ndimage.binary_propagation(seeds, mask=background)
    enclosed = background & (~reachable)
    return bool(enclosed.any())


def _exclude_insets(cx: float, cy: float, *, plot: PlotBox) -> bool:
    """Return True if point is inside known inset regions (heuristic).

    Fig. 2 contains two inset panels; exclude approximate plot-box fractions to
    avoid incorrectly ingesting inset markers.
    """

    px = (float(cx) - float(plot.left)) / float(plot.width())
    py = (float(cy) - float(plot.top)) / float(plot.height())

    # Top-left inset.
    if (0.12 <= px <= 0.47) and (0.05 <= py <= 0.36):
        return True

    # Bottom-right inset.
    if (0.60 <= px <= 0.95) and (0.60 <= py <= 0.92):
        return True

    return False


def _connected_marker_components(
    gray: np.ndarray,
    *,
    plot: PlotBox,
    dark_threshold: int,
    min_area: int,
    max_area: int,
    opening_kernel: int,
    opening_iterations: int,
) -> list[tuple[float, float, int, int, int, float, float, bool]]:
    """Return candidate components.

    Tuple: (cx, cy, area, bbox_w, bbox_h, fill_ratio, circularity, has_hole)
    where circularity = 4*pi*A / P^2 (P is boundary pixel count).
    """

    sub = gray[plot.top : plot.bottom, plot.left : plot.right]
    mask = sub < float(dark_threshold)

    if int(opening_iterations) > 0:
        k = int(opening_kernel)
        mask = ndimage.binary_opening(mask, structure=np.ones((k, k), dtype=bool), iterations=int(opening_iterations))

    lbl, n = ndimage.label(mask)
    if n <= 0:
        return []

    comps: list[tuple[float, float, int, int, int, float, float, bool]] = []
    slices = ndimage.find_objects(lbl)
    for idx, sl in enumerate(slices, start=1):
        if sl is None:
            continue
        ys, xs = sl
        comp = lbl[ys, xs] == idx

        area = int(comp.sum())
        if area < int(min_area) or area > int(max_area):
            continue

        h = int(ys.stop - ys.start)
        w = int(xs.stop - xs.start)
        if h <= 1 or w <= 1:
            continue

        ar = float(w) / float(h)
        if ar < 0.70 or ar > 1.45:
            continue

        fill_ratio = float(area) / float(h * w)
        if fill_ratio < 0.18:
            continue

        er = ndimage.binary_erosion(comp)
        boundary = comp & (~er)
        perim = float(int(boundary.sum()))
        if perim <= 0.0:
            continue

        circularity = float(4.0 * float(np.pi) * float(area) / (perim * perim))
        if circularity < 0.45:
            continue

        yy, xx = np.nonzero(comp)
        cx = float(xx.mean()) + float(xs.start) + float(plot.left)
        cy = float(yy.mean()) + float(ys.start) + float(plot.top)

        has_hole = _has_enclosed_hole(comp)
        comps.append((cx, cy, area, w, h, fill_ratio, circularity, bool(has_hole)))

    comps.sort(key=lambda t: (t[0], t[1]))
    return comps


def _pixel_to_data(
    cx: float,
    cy: float,
    *,
    plot: PlotBox,
    xmin: float,
    xmax: float,
    ymin: float,
    ymax: float,
) -> tuple[float, float]:
    k = float(xmin) + (float(cx) - float(plot.left)) / float(plot.width()) * (float(xmax) - float(xmin))
    omega = float(ymax) - (float(cy) - float(plot.top)) / float(plot.height()) * (float(ymax) - float(ymin))
    return float(k), float(omega)


def _render_csv_text(points: list[dict[str, float]]) -> str:
    header = ["k_um_inv", "omega_over_2pi_kHz"]

    def f(x: float) -> str:
        return ("%.12g" % float(x))

    lines = [",".join(header)]
    for p in points:
        lines.append(",".join([f(float(p[h])) for h in header]))
    return "\n".join(lines) + "\n"


def _select_points_deterministic(
    pts: list[tuple[float, float]],
    *,
    target_n: int,
    lowk_max: float = 1.5,
    lowk_required: int = 10,
    kmax_required: float = 3.0,
) -> list[tuple[float, float]]:
    """Deterministically downselect points while preserving coverage.

    Intent
    - Keep dense low-k coverage when possible.
    - Ensure we include at least one high-k point.
    - Avoid subjective cherry-picking by using quantile selection.
    """

    if target_n < 6:
        raise ValueError("target_n must be >= 6")

    pts_sorted = sorted(pts, key=lambda t: (t[0], t[1]))
    if not pts_sorted:
        return []

    low = [p for p in pts_sorted if p[0] <= float(lowk_max)]
    mid = [p for p in pts_sorted if float(lowk_max) < p[0] < float(kmax_required)]
    high = [p for p in pts_sorted if p[0] >= float(kmax_required)]

    # Relax gates if the series is sparse.
    if len(low) < int(lowk_required):
        lowk_required = max(6, min(len(low), int(lowk_required)))
    if not high:
        # Fall back to guaranteeing the max-k point.
        kmax_required = max(p[0] for p in pts_sorted)
        high = [p for p in pts_sorted if p[0] >= float(kmax_required) - 1e-12]

    # Allocate counts with priority to low-k.
    n_low = min(max(int(lowk_required), int(round(0.55 * target_n))), len(low))
    n_high = min(max(2, int(round(0.18 * target_n))), len(high))
    n_mid = max(0, target_n - n_low - n_high)

    if n_mid > len(mid):
        deficit = n_mid - len(mid)
        n_mid = len(mid)
        n_high = min(len(high), n_high + deficit)
        short = target_n - (n_low + n_mid + n_high)
        if short > 0:
            n_low = min(len(low), n_low + short)

    def pick_quantiles(seq: list[tuple[float, float]], n: int) -> list[tuple[float, float]]:
        if n <= 0:
            return []
        if n >= len(seq):
            return list(seq)
        out: list[tuple[float, float]] = []
        for j in range(n):
            q = 0.0 if n == 1 else (j / float(n - 1))
            i = int(round(q * (len(seq) - 1)))
            out.append(seq[i])

        # De-dup while preserving order.
        ded: list[tuple[float, float]] = []
        seen: set[tuple[float, float]] = set()
        for p in out:
            if p in seen:
                continue
            seen.add(p)
            ded.append(p)
        return ded

    chosen = pick_quantiles(low, n_low) + pick_quantiles(mid, n_mid) + pick_quantiles(high, n_high)
    chosen = sorted(chosen, key=lambda t: (t[0], t[1]))

    # Ensure we include the max-k point.
    max_k_pt = max(pts_sorted, key=lambda t: t[0])
    if max_k_pt not in chosen:
        chosen.append(max_k_pt)
        chosen.sort(key=lambda t: (t[0], t[1]))

    # Enforce strict monotonic k by pruning near-duplicates.
    pruned: list[tuple[float, float]] = []
    last_k = -1.0
    for k, w in chosen:
        if k <= last_k + 1e-9:
            continue
        pruned.append((k, w))
        last_k = k

    if len(pruned) < 6:
        raise RuntimeError(f"Selection produced too few points: N={len(pruned)}")
    return pruned


def _rows_preview(points: list[dict[str, float]], *, limit: int = 10) -> list[dict[str, float]]:
    out: list[dict[str, float]] = []
    for p in points[: int(limit)]:
        out.append({"k_um_inv": float(p["k_um_inv"]), "omega_over_2pi_kHz": float(p["omega_over_2pi_kHz"])})
    return out


def _digitize_from_png(*, png_path: Path) -> dict[str, Any]:
    rgb = np.array(Image.open(png_path).convert("RGB"))
    gray = _to_gray(rgb)

    plot = _find_plot_box(gray, dark_threshold=80)

    # Axis ranges (read off the figure; deterministic constants).
    xmin, xmax = 0.0, 4.5
    ymin, ymax = 0.0, 2.0

    comps = _connected_marker_components(
        gray,
        plot=plot,
        dark_threshold=120,
        min_area=10,
        max_area=4000,
        opening_kernel=2,
        opening_iterations=1,
    )

    # Stable marker signatures on the pinned zoom=4 render.
    # These are used instead of hole-detection, which is not robust after
    # binarization/opening on this figure.
    #
    # - Filled circles: (area=50, bbox=10x10, fill_ratio≈0.5)
    # - Open circles:   (area=85, bbox=14x19, fill_ratio≈0.32)
    sig_filled = (50, 10, 10)
    sig_open = (85, 14, 19)

    # Tighten to plausible marker components (empirically validated on the pinned render).
    # This rejects a large amount of non-marker noise deterministically.
    comps = [
        c
        for c in comps
        if (not _exclude_insets(c[0], c[1], plot=plot))
        and (40 <= int(c[2]) <= 120)
        and (7 <= int(c[3]) <= 25)
        and (7 <= int(c[4]) <= 25)
    ]

    pts_A_all: list[tuple[float, float]] = []
    pts_B_all: list[tuple[float, float]] = []

    n_exact_A = 0
    n_exact_B = 0
    n_fallback_A = 0
    n_fallback_B = 0

    for (cx, cy, area, bw, bh, fill_ratio, _circ, _has_hole) in comps:

        sig = (int(area), int(bw), int(bh))
        k, omega = _pixel_to_data(cx, cy, plot=plot, xmin=xmin, xmax=xmax, ymin=ymin, ymax=ymax)

        # Exact signature match is authoritative (extremely stable on the pinned render).
        if sig == sig_filled:
            pts_A_all.append((k, omega))
            n_exact_A += 1
            continue
        if sig == sig_open:
            pts_B_all.append((k, omega))
            n_exact_B += 1
            continue

        # Fallback for resilience if signatures drift slightly (e.g., different zoom):
        # open circles occupy a larger bbox with much lower fill ratio.
        if float(fill_ratio) >= 0.45:
            pts_A_all.append((k, omega))
            n_fallback_A += 1
        elif float(fill_ratio) <= 0.38:
            pts_B_all.append((k, omega))
            n_fallback_B += 1
        else:
            continue

    if len(pts_A_all) < 6:
        raise RuntimeError(f"Too few filled-circle candidates found for condition_A: N={len(pts_A_all)}")
    if len(pts_B_all) < 6:
        raise RuntimeError(f"Too few open-circle candidates found for condition_B: N={len(pts_B_all)}")

    # Deterministic downselection to avoid ingesting spurious components.
    pts_A = _select_points_deterministic(pts_A_all, target_n=25)
    pts_B = _select_points_deterministic(pts_B_all, target_n=25)

    def to_points(xs: list[tuple[float, float]]) -> list[dict[str, float]]:
        out: list[dict[str, float]] = []
        for (k, omega) in xs:
            out.append({"k_um_inv": float(k), "omega_over_2pi_kHz": float(omega)})
        out.sort(key=lambda d: (float(d["k_um_inv"]), float(d["omega_over_2pi_kHz"])))
        return out

    points_A = to_points(pts_A)
    points_B = to_points(pts_B)

    # Defensive uniqueness checks (rounded data-space collisions are suspicious).
    ra = {(round(float(p["k_um_inv"]), 6), round(float(p["omega_over_2pi_kHz"]), 6)) for p in points_A}
    rb = {(round(float(p["k_um_inv"]), 6), round(float(p["omega_over_2pi_kHz"]), 6)) for p in points_B}
    if len(ra) != len(points_A):
        raise RuntimeError("Non-unique digitized points for condition_A (data-space collision)")
    if len(rb) != len(points_B):
        raise RuntimeError("Non-unique digitized points for condition_B (data-space collision)")

    return {
        "plot_box": {"left": int(plot.left), "right": int(plot.right), "top": int(plot.top), "bottom": int(plot.bottom)},
        "axis_ranges": {"k_um_inv": [float(xmin), float(xmax)], "omega_over_2pi_kHz": [float(ymin), float(ymax)]},
        "discriminator_rule_id": "signature_split_v1",
        "marker_signatures_used": {
            "condition_A_filled": {"area": 50, "bbox_w": 10, "bbox_h": 10, "fill_ratio_approx": 0.50},
            "condition_B_open": {"area": 85, "bbox_w": 14, "bbox_h": 19, "fill_ratio_approx": 0.32},
        },
        "marker_prefilter": {
            "area_range": [40, 120],
            "bbox_w_range": [7, 25],
            "bbox_h_range": [7, 25],
            "fill_ratio_fallback": {"filled_ge": 0.45, "open_le": 0.38},
        },
        "classification_counts": {
            "exact": {"condition_A": int(n_exact_A), "condition_B": int(n_exact_B)},
            "fallback": {"condition_A": int(n_fallback_A), "condition_B": int(n_fallback_B)},
        },
        "condition_A": {"point_count": int(len(points_A)), "points": points_A},
        "condition_B": {"point_count": int(len(points_B)), "points": points_B},
    }


def write_ovbr03n_digitized_artifacts(*, date: str = "2026-01-25", force_redigitize: bool = False) -> dict[str, Path]:
    repo_root = _find_repo_root(Path(__file__))

    base = repo_root / "formal" / "external_evidence" / "bec_bragg_shammass_2012" / "ovbr03n_digitization"
    base.mkdir(parents=True, exist_ok=True)

    png_rel = "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png"
    pdf_rel = "formal/external_evidence/bec_bragg_shammass_2012/source.pdf"

    png_path = repo_root / Path(png_rel)
    pdf_path = repo_root / Path(pdf_rel)

    outA = base / "k_omega_conditionA.csv"
    outB = base / "k_omega_conditionB.csv"
    meta_path = base / "k_omega_digitization.metadata.json"

    if (not force_redigitize) and outA.exists() and outB.exists() and meta_path.exists():
        # Lightweight reuse: validate that metadata points at expected inputs and that the CSV hashes match.
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        if meta.get("schema") != "OV-BR-03N_k_omega_digitization_metadata/v1":
            raise RuntimeError("Existing OV-BR-03N metadata has unexpected schema; rerun with force_redigitize=True")
        if meta.get("source", {}).get("png_relpath") != png_rel:
            raise RuntimeError("Existing OV-BR-03N metadata points at a different PNG; rerun with force_redigitize=True")

        a_text = outA.read_text(encoding="utf-8")
        b_text = outB.read_text(encoding="utf-8")
        if meta.get("condition_A", {}).get("csv_sha256") != _sha256_text(a_text):
            raise RuntimeError("condition_A CSV sha mismatch vs metadata; rerun with force_redigitize=True")
        if meta.get("condition_B", {}).get("csv_sha256") != _sha256_text(b_text):
            raise RuntimeError("condition_B CSV sha mismatch vs metadata; rerun with force_redigitize=True")

        return {"conditionA_csv": outA, "conditionB_csv": outB, "metadata": meta_path}

    if not png_path.exists():
        raise FileNotFoundError(f"Missing expected rendered page PNG: {png_path.as_posix()}")
    if not pdf_path.exists():
        raise FileNotFoundError(f"Missing expected pinned PDF: {pdf_path.as_posix()}")

    dig = _digitize_from_png(png_path=png_path)

    points_A = list(dig["condition_A"]["points"])
    points_B = list(dig["condition_B"]["points"])

    a_text = _render_csv_text(points_A)
    b_text = _render_csv_text(points_B)

    outA.write_text(a_text, encoding="utf-8")
    outB.write_text(b_text, encoding="utf-8")

    meta_payload: dict[str, Any] = {
        "schema": "OV-BR-03N_k_omega_digitization_metadata/v1",
        "date": str(date),
        "source": {
            "pdf_relpath": pdf_rel,
            "pdf_sha256": _sha256_file(pdf_path),
            "png_relpath": png_rel,
            "png_sha256": _sha256_file(png_path),
        },
        "digitization": {
            "method": "deterministic_connected_components_centroids",
            "classifier": "signature_split_v1",
            "discriminator_rule_id": str(dig.get("discriminator_rule_id")),
            "marker_signatures_used": dig.get("marker_signatures_used"),
            "marker_prefilter": dig.get("marker_prefilter"),
            "classification_counts": dig.get("classification_counts"),
            "plot_box": dig["plot_box"],
            "axis_ranges": dig["axis_ranges"],
        },
        "condition_A": {
            "semantic": "filled circles",
            "csv_relpath": str(outA.relative_to(repo_root).as_posix()),
            "row_count": int(len(points_A)),
            "csv_sha256": _sha256_text(a_text),
            "rows_preview": _rows_preview(points_A, limit=10),
        },
        "condition_B": {
            "semantic": "open circles",
            "csv_relpath": str(outB.relative_to(repo_root).as_posix()),
            "row_count": int(len(points_B)),
            "csv_sha256": _sha256_text(b_text),
            "rows_preview": _rows_preview(points_B, limit=10),
        },
    }

    meta_path.write_text(json.dumps(meta_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {"conditionA_csv": outA, "conditionB_csv": outB, "metadata": meta_path}


@dataclass(frozen=True)
class OVBR03NDigitizedDispersionRecord:
    schema: str
    digitization_id: str
    date: str

    observable_id: str

    source: dict[str, Any]
    dataset: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "digitization_id": str(self.digitization_id),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "source": self.source,
            "dataset": self.dataset,
            "scope_limits": list(self.scope_limits),
        }

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["record_fingerprint"] = self.fingerprint()
        return d

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())


def ovbr03n_digitized_dispersion_record(*, date: str = "2026-01-25") -> OVBR03NDigitizedDispersionRecord:
    repo_root = _find_repo_root(Path(__file__))

    paths = write_ovbr03n_digitized_artifacts(date=str(date), force_redigitize=False)
    meta = json.loads(Path(paths["metadata"]).read_text(encoding="utf-8"))

    rec = OVBR03NDigitizedDispersionRecord(
        schema="OV-BR-03N/v1",
        digitization_id="OV-BR-03N",
        date=str(date),
        observable_id="OV-BR-03N",
        source=dict(meta["source"]),
        dataset={
            "axis_ranges": dict(meta["digitization"]["axis_ranges"]),
            "condition_A": {
                "semantic": str(meta["condition_A"]["semantic"]),
                "csv_relpath": str(meta["condition_A"]["csv_relpath"]),
                "row_count": int(meta["condition_A"]["row_count"]),
                "csv_sha256": str(meta["condition_A"]["csv_sha256"]),
                "rows_preview": list(meta["condition_A"]["rows_preview"]),
            },
            "condition_B": {
                "semantic": str(meta["condition_B"]["semantic"]),
                "csv_relpath": str(meta["condition_B"]["csv_relpath"]),
                "row_count": int(meta["condition_B"]["row_count"]),
                "csv_sha256": str(meta["condition_B"]["csv_sha256"]),
                "rows_preview": list(meta["condition_B"]["rows_preview"]),
            },
        },
        scope_limits=[
            "Digitized point ingestion only; no fitting or parameter inference.",
            "Two conditions are treated as separate series; no averaging.",
            "Inset panels are excluded by fixed plot-box fraction masks.",
        ],
    )

    return rec


def render_ovbr03n_digitized_lock_markdown(record: OVBR03NDigitizedDispersionRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-03N — Digitized Bragg dispersion ω(k) (two conditions) (computed)\n\n"
        "Scope / limits\n"
        "- Digitized point ingestion only; no fitting or parameter inference\n"
        "- Two conditions are treated as separate series; no averaging\n"
        "- Inset panels excluded by fixed masks\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr03n_digitized_lock(*, lock_path: Path | None = None, date: str = "2026-01-25") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-BR-03_bragg_dispersion_k_omega_digitized.md"

    rec = ovbr03n_digitized_dispersion_record(date=str(date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr03n_digitized_lock_markdown(rec), encoding="utf-8")
    return out
