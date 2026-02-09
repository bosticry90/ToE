"""OV-SND-02B: derived sound speed from OV-SND-01N2 seriesB distance-vs-time points (computed lock).

Purpose
- Provide a *second* sound-speed condition derived from the same pinned Andrews source,
  using a deterministic series split in OV-SND-01N2.

Input
- Frozen OV-SND-01N2 seriesB CSV: distance_vs_time_squares_seriesB.csv

Output
- Estimated sound speed c with uncertainty.

Pinned method (no free creativity)
- Primary estimator: constrained-through-origin least squares for y = c * t.
- Uncertainty: standard error of slope under a homoscedastic residual model.

Scope / limits
- Bookkeeping only; no ToE validation claim.
- If OV-SND-01N2 is BLOCKED, this record is BLOCKED.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.toe.observables.ovsnd01n2_sound_propagation_distance_time_digitized import (
    ovsnd01n2_digitized_propagation_dataset_record,
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


@dataclass(frozen=True)
class OVSND02BSoundSpeedFromPropagationRecord:
    schema: str
    date: str

    observable_id: str

    status: dict[str, Any]
    units: dict[str, Any] | None
    input_dataset: dict[str, Any] | None
    method: dict[str, Any] | None
    results: dict[str, Any] | None
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "units": None if self.units is None else dict(self.units),
            "input_dataset": None if self.input_dataset is None else dict(self.input_dataset),
            "method": None if self.method is None else dict(self.method),
            "results": None if self.results is None else dict(self.results),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsnd02b_sound_speed_from_propagation_record(*, date: str = "2026-01-24") -> OVSND02BSoundSpeedFromPropagationRecord:
    repo_root = _find_repo_root(Path(__file__))

    snd01n2 = ovsnd01n2_digitized_propagation_dataset_record(date=str(date))

    blockers: list[str] = []
    if bool(snd01n2.status.get("blocked")):
        blockers.append("missing_or_blocked_ov_snd_01n2")

    dataset_b = None
    if snd01n2.dataset is not None:
        dataset_b = snd01n2.dataset.get("seriesB")

    if dataset_b is None:
        blockers.append("missing_seriesB_dataset")

    status = {"blocked": bool(len(blockers) > 0), "blockers": list(blockers)}

    if status["blocked"]:
        return OVSND02BSoundSpeedFromPropagationRecord(
            schema="OV-SND-02B_sound_speed_from_propagation_seriesB/v1",
            date=str(date),
            observable_id="OV-SND-02B",
            status=status,
            units=None,
            input_dataset=None,
            method=None,
            results=None,
            scope_limits=[
                "derived_from_frozen_points_only",
                "no_manual_clicking",
                "pinned_slope_rule",
                "non_decisive_by_design",
            ],
        )

    csv_rel = str(dataset_b["csv_relpath"])
    csv_path = repo_root / csv_rel

    t_ms, d_um = _read_distance_time_csv(csv_path)
    through0 = _ols_through_origin(t_ms, d_um)

    c_m_per_s = float(through0["c_um_per_ms"]) * 1.0e-3
    se_m_per_s = float(through0["se_um_per_ms"]) * 1.0e-3

    input_dataset = {
        "source_digitization_id": str(snd01n2.digitization_id),
        "source_observable_id": str(snd01n2.observable_id),
        "source_series": "seriesB",
        "csv_relpath": csv_rel,
        "csv_sha256": str(dataset_b["csv_sha256"]),
        "row_count": int(dataset_b["row_count"]),
        "locked_record_fingerprint": str(snd01n2.fingerprint()),
        "locked_record_schema": str(snd01n2.schema),
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
        "density_dependence": {
            "status": "not_inferred",
            "note": "This record does not infer density n; mapping to density conditions is governed separately (OV-BR-SND-02).",
        },
    }

    return OVSND02BSoundSpeedFromPropagationRecord(
        schema="OV-SND-02B_sound_speed_from_propagation_seriesB/v1",
        date=str(date),
        observable_id="OV-SND-02B",
        status=status,
        units={
            "time": "ms",
            "distance": "um",
            "c": "m_per_s",
            "c_raw": "um_per_ms",
        },
        input_dataset=input_dataset,
        method=method,
        results=results,
        scope_limits=[
            "derived_from_frozen_points_only",
            "no_manual_clicking",
            "pinned_slope_rule",
            "no_density_inference",
            "non_decisive_by_design",
        ],
    )


def render_ovsnd02b_lock_markdown(record: OVSND02BSoundSpeedFromPropagationRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SND-02B — Derived sound speed from propagation (seriesB) (computed)\n\n"
        "Scope / limits\n"
        "- Derived from frozen OV-SND-01N2 seriesB points only\n"
        "- Pinned slope rule; no free creativity; no density inference\n"
        "- Non-decisive by design\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsnd02b_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SND-02B_sound_speed_from_propagation_seriesB.md"

    rec = ovsnd02b_sound_speed_from_propagation_record(date=str(date))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsnd02b_lock_markdown(rec), encoding="utf-8")
    return out
