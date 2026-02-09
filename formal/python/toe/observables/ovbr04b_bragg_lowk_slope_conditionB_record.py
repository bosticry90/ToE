"""OV-BR-04B: derived low-k Bragg slope for condition_B (computed lock).

See OV-BR-04A for the shared design constraints and pinned methodology.

Differences
- Uses OV-BR-03N condition_B (open circles) digitized points.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.toe.constraints.admissibility_manifest import check_required_gates
from formal.python.toe.observables.ovbr03n_bragg_dispersion_k_omega_digitized import (
    ovbr03n_digitized_dispersion_record,
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


def _read_k_omega_csv(csv_path: Path) -> tuple[np.ndarray, np.ndarray]:
    ks: list[float] = []
    ys: list[float] = []

    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.DictReader(f)
        if r.fieldnames != ["k_um_inv", "omega_over_2pi_kHz"]:
            raise ValueError(f"Unexpected columns: {r.fieldnames}")
        for row in r:
            ks.append(float(row["k_um_inv"]))
            ys.append(float(row["omega_over_2pi_kHz"]))

    x = np.asarray(ks, dtype=float)
    y = np.asarray(ys, dtype=float)

    if x.ndim != 1 or y.ndim != 1 or x.size != y.size or x.size < 6:
        raise ValueError("Invalid dataset")
    if not np.all(np.isfinite(x)) or not np.all(np.isfinite(y)):
        raise ValueError("Non-finite values in dataset")

    if not np.all(np.diff(x) >= -1e-12):
        raise ValueError("k values not monotone non-decreasing")

    return x, y


def _select_lowk_window_v1(x: np.ndarray, y: np.ndarray) -> tuple[np.ndarray, np.ndarray, list[dict[str, float]]]:
    k_max = 1.0
    omega_min = 0.1
    omega_max = 1.3

    mask = (x <= float(k_max)) & (y >= float(omega_min)) & (y <= float(omega_max))
    xs = x[mask]
    ys = y[mask]

    if xs.size < 5:
        raise RuntimeError("Insufficient points after lowk_window_v1 selection")

    preview = [{"k_um_inv": float(k), "omega_over_2pi_kHz": float(w)} for k, w in zip(xs.tolist(), ys.tolist())]
    return xs, ys, preview


def _ols_through_origin(x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    denom = float(np.dot(x, x))
    if denom <= 0.0:
        raise ValueError("Degenerate x vector")

    s = float(np.dot(x, y) / denom)
    resid = y - s * x

    n = int(x.size)
    dof = n - 1
    s2 = float(np.dot(resid, resid) / float(dof)) if dof > 0 else float("nan")
    se_s = float(np.sqrt(s2 / denom))

    return {
        "s_kHz_per_um_inv": float(s),
        "se_kHz_per_um_inv": float(se_s),
        "n": float(n),
        "dof": float(dof),
        "residual_rms_kHz": float(np.sqrt(np.mean(resid**2))),
    }


def _ols_with_intercept(x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    X = np.column_stack([np.ones_like(x), x])
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    a = float(beta[0])
    s = float(beta[1])

    resid = y - (a + s * x)
    n = int(x.size)
    dof = n - 2
    s2 = float(np.dot(resid, resid) / float(dof)) if dof > 0 else float("nan")

    XtX_inv = np.linalg.inv(X.T @ X)
    se_a = float(np.sqrt(s2 * XtX_inv[0, 0]))
    se_s = float(np.sqrt(s2 * XtX_inv[1, 1]))

    ybar = float(np.mean(y))
    ss_tot = float(np.dot(y - ybar, y - ybar))
    sse = float(np.dot(resid, resid))
    r2 = 1.0 - (sse / ss_tot if ss_tot > 0.0 else 0.0)

    return {
        "a_kHz": float(a),
        "se_a_kHz": float(se_a),
        "s_kHz_per_um_inv": float(s),
        "se_kHz_per_um_inv": float(se_s),
        "n": float(n),
        "dof": float(dof),
        "residual_rms_kHz": float(np.sqrt(np.mean(resid**2))),
        "r2": float(r2),
    }


@dataclass(frozen=True)
class OVBR04BLowKSlopeRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]
    condition_key: str
    condition_semantic: str

    units: dict[str, Any]
    input_dataset: dict[str, Any]
    selection: dict[str, Any]
    method: dict[str, Any]
    results: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "condition_key": str(self.condition_key),
            "condition_semantic": str(self.condition_semantic),
            "units": dict(self.units),
            "input_dataset": dict(self.input_dataset),
            "selection": dict(self.selection),
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


def ovbr04b_bragg_lowk_slope_conditionB_record(*, date: str = "2026-01-25", admissibility_manifest_path: Path | None = None) -> OVBR04BLowKSlopeRecord:
    repo_root = _find_repo_root(Path(__file__))

    required_gates = ["CT01", "SYM01", "CAUS01"]
    gate_check = check_required_gates(repo_root=repo_root, required_gate_ids=required_gates, manifest_path=admissibility_manifest_path)
    debug = {
        "manifest_input_path": str(admissibility_manifest_path) if admissibility_manifest_path else None,
        "manifest_resolved_path": str(gate_check.manifest_path),
        "manifest_version": gate_check.manifest_version,
        "manifest_sha256": gate_check.manifest_sha256,
    }
    status = {
        "blocked": bool(gate_check.blocked),
        "reasons": list(gate_check.reasons),
        "required_gates": list(required_gates),
        "admissibility_manifest": {
            "path": str(gate_check.manifest_path),
            "version": gate_check.manifest_version,
        },
        "debug": debug,
    }
    if gate_check.blocked:
        selection = {
            "rule_id": "lowk_window_v1",
            "parameters": {
                "k_um_inv_max": 1.0,
                "omega_over_2pi_kHz_min": 0.1,
                "omega_over_2pi_kHz_max": 1.3,
            },
        }
        return OVBR04BLowKSlopeRecord(
            schema="OV-BR-04B_bragg_lowk_slope_conditionB/v2",
            date=str(date),
            observable_id="OV-BR-04B",
            status=status,
            condition_key="condition_B",
            condition_semantic="blocked",
            units={},
            input_dataset={},
            selection=selection,
            method={},
            results={},
            scope_limits=[
                "blocked_by_admissibility_manifest",
                "requires_CT01_SYM01_CAUS01",
            ],
        )

    br03n = ovbr03n_digitized_dispersion_record(date=str(date))
    cb = br03n.dataset["condition_B"]

    csv_rel = str(cb["csv_relpath"])
    csv_path = repo_root / csv_rel

    x_all, y_all = _read_k_omega_csv(csv_path)
    x_sel, y_sel, preview = _select_lowk_window_v1(x_all, y_all)

    through0 = _ols_through_origin(x_sel, y_sel)
    with_int = _ols_with_intercept(x_sel, y_sel)

    input_dataset = {
        "source_digitization_id": str(br03n.digitization_id),
        "source_observable_id": str(br03n.observable_id),
        "condition_key": "condition_B",
        "condition_semantic": str(cb.get("semantic")),
        "csv_relpath": csv_rel,
        "csv_sha256": str(cb["csv_sha256"]),
        "row_count": int(cb["row_count"]),
        "locked_record_schema": str(br03n.schema),
        "locked_record_fingerprint": str(br03n.fingerprint()),
        "source_png_relpath": str(br03n.source["png_relpath"]),
        "source_png_sha256": str(br03n.source["png_sha256"]),
    }

    selection = {
        "rule_id": "lowk_window_v1",
        "parameters": {
            "k_um_inv_max": 1.0,
            "omega_over_2pi_kHz_min": 0.1,
            "omega_over_2pi_kHz_max": 1.3,
        },
        "selected_row_count": int(x_sel.size),
        "rows_preview": list(preview),
    }

    method = {
        "primary": {
            "name": "ols_through_origin",
            "model": "omega_over_2pi_kHz = s_kHz_per_um_inv * k_um_inv",
            "rationale": "Pinned conservative estimator; avoids free intercept; physical expectation omega→0 as k→0.",
        },
        "uncertainty": {
            "type": "slope_standard_error",
            "assumptions": ["homoscedastic_residuals", "independent_points"],
        },
        "diagnostic": {
            "name": "ols_with_intercept",
            "model": "omega_over_2pi_kHz = a_kHz + s_kHz_per_um_inv * k_um_inv",
            "used_for": "sanity_check_only",
        },
    }

    c_mm_per_s = float(through0["s_kHz_per_um_inv"])
    se_mm_per_s = float(through0["se_kHz_per_um_inv"])

    results = {
        "primary": {
            "s_kHz_per_um_inv": float(through0["s_kHz_per_um_inv"]),
            "se_kHz_per_um_inv": float(through0["se_kHz_per_um_inv"]),
            "c_mm_per_s": float(c_mm_per_s),
            "se_mm_per_s": float(se_mm_per_s),
            "n": int(through0["n"]),
            "dof": int(through0["dof"]),
            "residual_rms_kHz": float(through0["residual_rms_kHz"]),
        },
        "diagnostic": {
            "a_kHz": float(with_int["a_kHz"]),
            "se_a_kHz": float(with_int["se_a_kHz"]),
            "s_kHz_per_um_inv": float(with_int["s_kHz_per_um_inv"]),
            "se_kHz_per_um_inv": float(with_int["se_kHz_per_um_inv"]),
            "n": int(with_int["n"]),
            "dof": int(with_int["dof"]),
            "residual_rms_kHz": float(with_int["residual_rms_kHz"]),
            "r2": float(with_int["r2"]),
        },
    }

    scope_limits = [
        "derived_from_frozen_points_only",
        "deterministic_selection_rule_only",
        "no_parameter_inference_beyond_slope",
        "no_cross_regime_averaging",
        "non_decisive_by_design",
    ]

    # Contract: if gates are admitted, results.primary must exist.
    if "primary" not in results:
        status_blocked = dict(status)
        status_blocked["blocked"] = True
        status_blocked["reasons"] = list(status_blocked.get("reasons", [])) + ["missing_results_primary"]
        return OVBR04BLowKSlopeRecord(
            schema="OV-BR-04B_bragg_lowk_slope_conditionB/v2",
            date=str(date),
            observable_id="OV-BR-04B",
            status=status_blocked,
            condition_key="condition_B",
            condition_semantic="blocked",
            units={},
            input_dataset=input_dataset,
            selection=selection,
            method=method,
            results={},
            scope_limits=list(scope_limits) + ["blocked_missing_results_primary"],
        )

    return OVBR04BLowKSlopeRecord(
        schema="OV-BR-04B_bragg_lowk_slope_conditionB/v2",
        date=str(date),
        observable_id="OV-BR-04B",
        status=status,
        condition_key="condition_B",
        condition_semantic=str(cb.get("semantic")),
        units={
            "k": "um_inv",
            "omega_over_2pi": "kHz",
            "slope": "kHz_per_um_inv",
            "velocity_candidate": "mm_per_s",
        },
        input_dataset=input_dataset,
        selection=selection,
        method=method,
        results=results,
        scope_limits=scope_limits,
    )


def render_ovbr04b_lock_markdown(record: OVBR04BLowKSlopeRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-04B — Bragg low-k slope (condition_B) (computed)\n\n"
        "Scope / limits\n"
        "- Derived from frozen OV-BR-03N points only\n"
        "- Deterministic low-k window + pinned slope rule\n"
        "- Bookkeeping / anchoring only; no ToE validation claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr04b_lock(*, lock_path: Path | None = None, date: str = "2026-01-25", admissibility_manifest_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-BR-04B_bragg_lowk_slope_conditionB.md"
        )

    rec = ovbr04b_bragg_lowk_slope_conditionB_record(date=str(date), admissibility_manifest_path=admissibility_manifest_path)

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr04b_lock_markdown(rec), encoding="utf-8")
    return out
