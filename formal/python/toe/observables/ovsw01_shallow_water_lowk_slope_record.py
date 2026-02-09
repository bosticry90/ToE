"""OV-SW-01: shallow-water lane low-k slope (computed lock).

Purpose
- Define the governance-safe ingestion + extraction point for the Axis C (shallow-water) lane.
- Compute a pinned through-origin low-k slope from a frozen digitized CSV.

Status discipline
- This record remains BLOCKED until the required frozen artifacts exist:
  - formal/external_evidence/shallow_water_TBD/ovsw01_digitization/omega_over_2pi_vs_k_lowk.csv
  - formal/external_evidence/shallow_water_TBD/ovsw01_digitization/omega_over_2pi_vs_k_lowk.metadata.json

Non-claims
- No cross-lane pairing, no comparability, no physical claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _read_k_f_csv(csv_path: Path) -> tuple[list[tuple[float, float]], str]:
    """Return (points, csv_sha256_of_text) after validating schema."""

    text = csv_path.read_text(encoding="utf-8")
    sha = _sha256_text(text)

    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        expected = ["k_m_inv", "f_s_inv"]
        if r.fieldnames != expected:
            raise ValueError(f"Unexpected columns: {r.fieldnames} (expected {expected})")

        pts: list[tuple[float, float]] = []
        for row in r:
            k = float(row["k_m_inv"])
            fval = float(row["f_s_inv"])
            if not (k == k and fval == fval):
                raise ValueError("Non-finite values present in omega_over_2pi_vs_k_lowk.csv")
            if k < 0.0:
                raise ValueError("Negative k_m_inv is not allowed")
            pts.append((k, fval))

    return pts, sha


def _ols_through_origin(x: list[float], y: list[float]) -> dict[str, float]:
    if len(x) != len(y):
        raise ValueError("x and y lengths do not match")
    n = int(len(x))
    if n < 2:
        raise ValueError("Need at least 2 points")

    sxx = 0.0
    sxy = 0.0
    for xi, yi in zip(x, y):
        sxx += float(xi) * float(xi)
        sxy += float(xi) * float(yi)

    if sxx == 0.0:
        raise ValueError("All k values are zero; cannot fit slope")

    b = sxy / sxx
    resid2 = 0.0
    for xi, yi in zip(x, y):
        r = float(yi) - b * float(xi)
        resid2 += r * r

    # Through-origin model has 1 parameter.
    dof = float(n - 1)
    sigma2 = resid2 / dof
    se_b = (sigma2 / sxx) ** 0.5

    return {
        "b": float(b),
        "se_b": float(se_b),
        "n": float(n),
        "dof": float(dof),
    }


def _points_preview(points: list[tuple[float, float]], *, limit: int = 10) -> list[dict[str, float]]:
    out: list[dict[str, float]] = []
    for k, fval in points[: int(limit)]:
        out.append({"k_m_inv": float(k), "f_s_inv": float(fval)})
    return out


@dataclass(frozen=True)
class OVSW01ShallowWaterLowkSlopeRecord:
    schema: str
    date: str
    observable_id: str

    status: dict[str, Any]
    input_dataset: dict[str, Any] | None
    method: dict[str, Any]
    results: dict[str, Any] | None
    scope_limits: list[str]
    units: dict[str, Any]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "input_dataset": (dict(self.input_dataset) if self.input_dataset is not None else None),
            "method": dict(self.method),
            "results": (dict(self.results) if self.results is not None else None),
            "scope_limits": list(self.scope_limits),
            "units": dict(self.units),
            # Keep a stable empty surface for future row-level exports.
            "rows": [],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsw01_shallow_water_lowk_slope_record(
    *,
    date: str = "2026-01-25",
) -> OVSW01ShallowWaterLowkSlopeRecord:
    repo_root = _find_repo_root(Path(__file__))

    csv_rel = "formal/external_evidence/shallow_water_TBD/ovsw01_digitization/omega_over_2pi_vs_k_lowk.csv"
    meta_rel = "formal/external_evidence/shallow_water_TBD/ovsw01_digitization/omega_over_2pi_vs_k_lowk.metadata.json"
    csv_path = repo_root / csv_rel
    meta_path = repo_root / meta_rel

    blockers: list[str] = []
    if not csv_path.exists():
        blockers.append("omega_over_2pi_vs_k_lowk_csv_missing")
    if not meta_path.exists():
        blockers.append("omega_over_2pi_vs_k_lowk_metadata_missing")

    points: list[tuple[float, float]] | None = None
    csv_sha: str | None = None
    if csv_path.exists():
        points, csv_sha = _read_k_f_csv(csv_path)
        if len(points) < 2:
            blockers.append("insufficient_points_for_lowk_slope (need>=2)")

    status = {"blocked": bool(len(blockers) > 0), "blockers": list(blockers)}

    input_dataset: dict[str, Any] | None = None
    if points is not None:
        input_dataset = {
            "csv_relpath": csv_rel,
            "metadata_relpath": meta_rel,
            "row_count": int(len(points)),
            "rows_preview": _points_preview(points, limit=10),
            "columns": [
                {"name": "k_m_inv", "unit": "m^-1", "dtype": "float"},
                {"name": "f_s_inv", "unit": "s^-1", "dtype": "float"},
            ],
            "csv_sha256": str(csv_sha) if csv_sha is not None else None,
        }

    method = {
        "primary": {
            "name": "ols_through_origin",
            "model": "f_s_inv = slope_s_inv_per_m_inv * k_m_inv",
            "rationale": "Pinned through-origin slope rule; avoids free intercept choice; no cross-lane interpretation.",
        },
        "uncertainty": {
            "type": "slope_standard_error",
            "assumptions": ["homoscedastic_residuals", "independent_points"],
        },
    }

    results: dict[str, Any] | None = None
    if not status["blocked"] and points is not None:
        x = [float(k) for k, _ in points]
        y = [float(fval) for _, fval in points]
        fit = _ols_through_origin(x, y)
        results = {
            "primary": {
                "slope_s_inv_per_m_inv": float(fit["b"]),
                "se_s_inv_per_m_inv": float(fit["se_b"]),
                "slope_m_per_s": float(fit["b"]),
                "se_m_per_s": float(fit["se_b"]),
                "n": float(fit["n"]),
                "dof": float(fit["dof"]),
            },
            "notes": "Dimensionally, (s^-1)/(m^-1) = m/s. This is lane-internal only.",
        }

    scope_limits = [
        "bookkeeping_only",
        "no_cross_lane_pairing",
        "no_physics_claim",
        "no_fitting_beyond_pinned_slope_rule",
        "no_intercept",
        "no_weighting",
        "non_decisive_by_design",
    ]

    units = {
        "k": "m^-1",
        "f": "s^-1",
        "slope": "m_per_s",
        "slope_raw": "s^-1_per_m^-1",
    }

    return OVSW01ShallowWaterLowkSlopeRecord(
        schema="OV-SW-01_shallow_water_lowk_slope/v1",
        date=str(date),
        observable_id="OV-SW-01",
        status=status,
        input_dataset=input_dataset,
        method=method,
        results=results,
        scope_limits=scope_limits,
        units=units,
    )


def render_ovsw01_lock_markdown(record: OVSW01ShallowWaterLowkSlopeRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SW-01 — Shallow-water low-k slope (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping-only Axis C lane ingestion + slope extraction\n"
        "- Pinned through-origin slope rule; no free intercept; no weighting\n"
        "- No cross-lane pairing or comparability; non-decisive by design\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsw01_lock(*, lock_path: Path | None = None, date: str = "2026-01-25") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SW-01_shallow_water_lowk_slope.md"
        )

    rec = ovsw01_shallow_water_lowk_slope_record(date=str(date))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsw01_lock_markdown(rec), encoding="utf-8")
    return out
