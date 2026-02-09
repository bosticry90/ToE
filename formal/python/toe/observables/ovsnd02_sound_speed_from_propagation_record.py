"""OV-SND-02: derived sound speed from OV-SND-01N distance-vs-time points (computed lock).

Purpose
- Promote the OV-SND-01N digitized distance-vs-time anchor into a directly
  interpretable sound-speed observable via a pinned, deterministic slope rule.

Input
- Frozen OV-SND-01N CSV: distance_vs_time_squares.csv

Output
- Estimated sound speed c with uncertainty.

Pinned method (no free creativity)
- Primary estimator: constrained-through-origin least squares for y = c * t
  using the frozen points.
- Uncertainty: standard error of slope under homoscedastic residual model.
- Additional (non-authoritative) diagnostic: unconstrained linear regression
  y = a + c*t.

Scope / limits
- Derived observable for bookkeeping only; no ToE validation claim.
- No density inference here; any density dependence remains symbolic (OV-SND-01).
- No continuity/averaging across regimes.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import (
    ovsnd01_digitized_propagation_dataset_record,
)


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _read_distance_time_csv(csv_path: Path) -> tuple[np.ndarray, np.ndarray]:
    # Deterministic CSV parse; no locale dependence.
    times: list[float] = []
    distances: list[float] = []

    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        if r.fieldnames != ["time_ms", "distance_um"]:
            raise ValueError(f"Unexpected columns: {r.fieldnames}")
        for row in r:
            times.append(float(row["time_ms"]))
            distances.append(float(row["distance_um"]))

    t = np.asarray(times, dtype=float)
    y = np.asarray(distances, dtype=float)

    if t.ndim != 1 or y.ndim != 1 or t.size != y.size or t.size < 3:
        raise ValueError("Invalid dataset")
    if not np.all(np.isfinite(t)) or not np.all(np.isfinite(y)):
        raise ValueError("Non-finite values in dataset")

    return t, y


def _ols_through_origin(t: np.ndarray, y: np.ndarray) -> dict[str, float]:
    # y ≈ c*t
    denom = float(np.dot(t, t))
    if denom <= 0:
        raise ValueError("Degenerate time vector")

    c = float(np.dot(t, y) / denom)
    resid = y - c * t

    n = int(t.size)
    dof = n - 1
    s2 = float(np.dot(resid, resid) / float(dof)) if dof > 0 else float("nan")
    se_c = float(np.sqrt(s2 / denom))

    return {
        "c_um_per_ms": float(c),
        "se_um_per_ms": float(se_c),
        "n": float(n),
        "dof": float(dof),
        "residual_rms_um": float(np.sqrt(np.mean(resid**2))),
    }


def _ols_with_intercept(t: np.ndarray, y: np.ndarray) -> dict[str, float]:
    # y ≈ a + c*t
    X = np.column_stack([np.ones_like(t), t])
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    a = float(beta[0])
    c = float(beta[1])

    resid = y - (a + c * t)
    n = int(t.size)
    dof = n - 2
    s2 = float(np.dot(resid, resid) / float(dof)) if dof > 0 else float("nan")

    XtX_inv = np.linalg.inv(X.T @ X)
    se_a = float(np.sqrt(s2 * XtX_inv[0, 0]))
    se_c = float(np.sqrt(s2 * XtX_inv[1, 1]))

    return {
        "a_um": float(a),
        "se_a_um": float(se_a),
        "c_um_per_ms": float(c),
        "se_um_per_ms": float(se_c),
        "n": float(n),
        "dof": float(dof),
        "residual_rms_um": float(np.sqrt(np.mean(resid**2))),
    }


@dataclass(frozen=True)
class OVSND02SoundSpeedFromPropagationRecord:
    schema: str
    date: str

    observable_id: str

    units: dict[str, Any]
    input_dataset: dict[str, Any]
    method: dict[str, Any]
    results: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "units": dict(self.units),
            "input_dataset": dict(self.input_dataset),
            "method": dict(self.method),
            "results": dict(self.results),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd02_sound_speed_from_propagation_record(*, date: str = "2026-01-24") -> OVSND02SoundSpeedFromPropagationRecord:
    repo_root = _find_repo_root(Path(__file__))

    snd01n = ovsnd01_digitized_propagation_dataset_record(date=str(date))
    csv_rel = str(snd01n.dataset["csv_relpath"])
    csv_path = repo_root / csv_rel

    t_ms, d_um = _read_distance_time_csv(csv_path)

    through0 = _ols_through_origin(t_ms, d_um)
    with_int = _ols_with_intercept(t_ms, d_um)

    # Unit conversions: 1 (um/ms) = 1e-3 (m/s)
    c_m_per_s = float(through0["c_um_per_ms"]) * 1.0e-3
    se_m_per_s = float(through0["se_um_per_ms"]) * 1.0e-3

    input_dataset = {
        "source_digitization_id": str(snd01n.digitization_id),
        "source_observable_id": str(snd01n.observable_id),
        "csv_relpath": csv_rel,
        "csv_sha256": str(snd01n.dataset["csv_sha256"]),
        "row_count": int(snd01n.dataset["row_count"]),
        "locked_record_fingerprint": str(snd01n.fingerprint()),
        "locked_record_schema": str(snd01n.schema),
    }

    method = {
        "primary": {
            "name": "ols_through_origin",
            "model": "distance_um = c_um_per_ms * time_ms",
            "rationale": "Pinned conservative estimator; avoids free intercept choice; physical expectation distance→0 at t→0.",
        },
        "uncertainty": {
            "type": "slope_standard_error",
            "assumptions": ["homoscedastic_residuals", "independent_points"],
        },
        "diagnostic": {
            "name": "ols_with_intercept",
            "model": "distance_um = a_um + c_um_per_ms * time_ms",
            "used_for": "sanity_check_only",
        },
    }

    results = {
        "primary": {
            "c_um_per_ms": float(through0["c_um_per_ms"]),
            "se_um_per_ms": float(through0["se_um_per_ms"]),
            "c_m_per_s": float(c_m_per_s),
            "se_m_per_s": float(se_m_per_s),
            "n": int(through0["n"]),
            "dof": int(through0["dof"]),
            "residual_rms_um": float(through0["residual_rms_um"]),
        },
        "diagnostic": {
            "a_um": float(with_int["a_um"]),
            "se_a_um": float(with_int["se_a_um"]),
            "c_um_per_ms": float(with_int["c_um_per_ms"]),
            "se_um_per_ms": float(with_int["se_um_per_ms"]),
            "n": int(with_int["n"]),
            "dof": int(with_int["dof"]),
            "residual_rms_um": float(with_int["residual_rms_um"]),
        },
        "density_dependence": {
            "status": "not_inferred",
            "note": "This record does not infer density n; symbolic scaling is recorded separately in OV-SND-01.",
        },
    }

    scope_limits = [
        "derived_from_frozen_points_only",
        "no_fitting_beyond_pinned_slope_rule",
        "no_density_inference",
        "no_parameter_inference_beyond_c",
        "no_continuity_claim",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    return OVSND02SoundSpeedFromPropagationRecord(
        schema="OV-SND-02_sound_speed_from_propagation/v1",
        date=str(date),
        observable_id="OV-SND-02",
        units={
            "time": "ms",
            "distance": "um",
            "c": "m_per_s",
            "c_raw": "um_per_ms",
        },
        input_dataset=input_dataset,
        method=method,
        results=results,
        scope_limits=scope_limits,
    )


def render_ovsnd02_lock_markdown(record: OVSND02SoundSpeedFromPropagationRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-02 — Derived sound speed from propagation (computed)\n\n"
        "Scope / limits\n"
        "- Derived from frozen OV-SND-01N points only\n"
        "- Pinned slope rule; no free creativity; no density inference\n"
        "- No continuity/averaging across regimes; non-decisive by design\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd02_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-02_sound_speed_from_propagation.md"

    rec = ovsnd02_sound_speed_from_propagation_record(date=str(date))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd02_lock_markdown(rec), encoding="utf-8")
    return out
