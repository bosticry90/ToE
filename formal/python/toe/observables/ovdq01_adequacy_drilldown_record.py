"""OV-DQ-01 adequacy drilldown record (bookkeeping only).

This record is intentionally diagnostic and non-blocking:
- It does not change DQ-01 thresholds or policy.
- It surfaces per-window metric vs threshold deltas/ratios.
- It emits a DS-02 scale/unit/mapping suspicion flag when the magnitude gap is
  extreme (triage only; no physics claim).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovdq01_dq01_diagnostics_record import (
    _find_repo_root,
    ovdq01_dq01_diagnostics_record,
)


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


_REASON_ORDER = (
    "missing_fit_quality",
    "n_points_lt_min",
    "rmse_gt_max",
    "c0_stderr_gt_max",
    "beta_not_identifiable",
    # v2/variantA strict clauses (kept for completeness; deterministic ordering)
    "rmse_gt_max_strict_4pt",
    "c0_stderr_gt_max_strict_4pt",
    "rmse_gt_max_n4_strict",
    "c0_stderr_gt_max_n4_strict",
    # informational codes
    "beta_ignored_low_n",
)


def _first_tripped_reason(reason_codes: list[str]) -> str | None:
    s = set(str(r) for r in reason_codes)
    for r in _REASON_ORDER:
        if r in s:
            return r
    return None


def _ratio_over_max(value: float, max_value: float) -> float:
    if max_value == 0.0:
        return float("inf") if value != 0.0 else 1.0
    return float(value / max_value)


def _ratio_under_min(value: float, min_value: float) -> float:
    if value == 0.0:
        return float("inf") if min_value > 0.0 else 1.0
    return float(min_value / value)


def _metric_block_max(*, name: str, value: float, max_value: float) -> dict[str, Any]:
    ratio = _ratio_over_max(value, max_value)
    tripped = bool(value > max_value)
    return {
        "name": name,
        "sense": "max",
        "value": float(value),
        "threshold": float(max_value),
        "delta": float(value - max_value),
        "ratio": float(ratio),
        "tripped": bool(tripped),
        "violation_ratio": float(ratio) if tripped else 1.0,
    }


def _metric_block_min(*, name: str, value: float, min_value: float) -> dict[str, Any]:
    ratio = _ratio_under_min(value, min_value)
    tripped = bool(value < min_value)
    return {
        "name": name,
        "sense": "min",
        "value": float(value),
        "threshold": float(min_value),
        "delta": float(value - min_value),
        "ratio": float(value / min_value) if min_value != 0.0 else float("inf"),
        "tripped": bool(tripped),
        "violation_ratio": float(ratio) if tripped else 1.0,
    }


def _metric_block_bool(*, name: str, value: bool) -> dict[str, Any]:
    return {
        "name": name,
        "sense": "bool",
        "value": bool(value),
        "threshold": True,
        "delta": None,
        "ratio": None,
        "tripped": bool(not value),
        "violation_ratio": 2.0 if (not value) else 1.0,
    }


def _dominant_by_violation(metrics: list[dict[str, Any]]) -> str | None:
    if not metrics:
        return None
    best = max(metrics, key=lambda m: float(m.get("violation_ratio", 1.0)))
    if float(best.get("violation_ratio", 1.0)) <= 1.0:
        return None
    return str(best.get("name"))


def _window_drilldown(window: dict[str, Any]) -> dict[str, Any]:
    dq01 = dict(window["dq01"])
    metrics = dict(dq01["metrics"])

    rmse = float(metrics["rmse_omega_over_k_m_per_s"])
    rmse_max = float(metrics["rmse_omega_over_k_max_m_per_s"])

    c0_stderr = float(metrics["c0_stderr_m_per_s"])
    c0_max = float(metrics["c0_stderr_max_m_per_s"])

    beta_snr = float(metrics["beta_snr"])
    snr_min = float(metrics["snr_beta_min"])

    n_points = float(metrics["n_points"])
    n_min = float(metrics["n_points_min"])

    beta_identifiable = bool(float(metrics["beta_identifiable"]) >= 0.5)
    beta_used = bool(float(metrics.get("beta_used_for_inference", 1.0)) >= 0.5)

    metric_blocks: list[dict[str, Any]] = [
        _metric_block_min(name="n_points", value=n_points, min_value=n_min),
        _metric_block_max(name="rmse_omega_over_k_m_per_s", value=rmse, max_value=rmse_max),
        _metric_block_max(name="c0_stderr_m_per_s", value=c0_stderr, max_value=c0_max),
        _metric_block_min(name="beta_snr", value=beta_snr, min_value=snr_min),
        _metric_block_bool(name="beta_identifiable", value=beta_identifiable),
        _metric_block_bool(name="beta_used_for_inference", value=beta_used),
    ]

    # For auditability: also provide ratios the user asked for explicitly.
    rmse_ratio = _ratio_over_max(rmse, rmse_max)
    c0_ratio = _ratio_over_max(c0_stderr, c0_max)

    reason_codes = [str(r) for r in dq01.get("reason_codes", [])]
    first_tripped = _first_tripped_reason(reason_codes)
    dominant = _dominant_by_violation(metric_blocks)

    return {
        "tag": str(window.get("tag", "")),
        "data_fingerprint": window.get("data_fingerprint", None),
        "dq01": {
            "passes": bool(dq01["passes"]),
            "reason_codes": reason_codes,
            "fingerprint": str(dq01["fingerprint"]),
            "input_fingerprint": str(dq01["input_fingerprint"]),
        },
        "metrics": {
            "rmse_omega_over_k_m_per_s": {
                "value": float(rmse),
                "max": float(rmse_max),
                "delta": float(rmse - rmse_max),
                "ratio": float(rmse_ratio),
            },
            "c0_stderr_m_per_s": {
                "value": float(c0_stderr),
                "max": float(c0_max),
                "delta": float(c0_stderr - c0_max),
                "ratio": float(c0_ratio),
            },
            "beta_snr": {
                "value": float(beta_snr),
                "min": float(snr_min),
                "delta": float(beta_snr - snr_min),
                "ratio": float(beta_snr / snr_min) if snr_min != 0.0 else float("inf"),
            },
            "beta_identifiable": {
                "value": bool(beta_identifiable),
            },
            "n_points": {
                "value": float(n_points),
                "min": float(n_min),
                "delta": float(n_points - n_min),
                "ratio": float(n_points / n_min) if n_min != 0.0 else float("inf"),
            },
        },
        "first_tripped_metric": first_tripped,
        "dominant_by_ratio": dominant,
        "metric_blocks": metric_blocks,
    }


def _scale_or_units_mismatch_suspected(windows: list[dict[str, Any]]) -> bool:
    # Triaging heuristic (non-blocking): flag if the magnitude blow-up strongly
    # suggests unit/mapping mismatch (e.g., Hz vs rad/s, um^-1 vs m^-1, etc.).
    extreme = 0
    for w in windows:
        m = w["metrics"]
        rmse_ratio = float(m["rmse_omega_over_k_m_per_s"]["ratio"])
        c0_ratio = float(m["c0_stderr_m_per_s"]["ratio"])
        if (rmse_ratio > 100.0) or (c0_ratio > 100.0):
            extreme += 1
    return extreme >= 2


@dataclass(frozen=True)
class OVDQ01AdequacyDrilldownRecord:
    schema: str
    adequacy_policy: str
    ov04x: dict[str, Any]
    ov03x: dict[str, Any]
    notes: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "adequacy_policy": str(self.adequacy_policy),
            "ov04x": self.ov04x,
            "ov03x": self.ov03x,
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def ovdq01_adequacy_drilldown_record(*, adequacy_policy: str = "DQ-01_v1") -> OVDQ01AdequacyDrilldownRecord:
    base = ovdq01_dq01_diagnostics_record(adequacy_policy=str(adequacy_policy))

    ov04_windows_raw = list(base.ov04x["curved_windows"])
    ov03_windows_raw = list(base.ov03x["curved_windows"])

    if len(ov04_windows_raw) == 0 or len(ov03_windows_raw) == 0:
        raise RuntimeError("OV-DQ-01 drilldown requires non-empty curved windows for OV-04x and OV-03x")

    ov04_windows = [_window_drilldown(w) for w in ov04_windows_raw]
    ov03_windows = [_window_drilldown(w) for w in ov03_windows_raw]

    ov04_flags: list[str] = []
    if _scale_or_units_mismatch_suspected(ov04_windows):
        ov04_flags.append("scale_or_units_mismatch_suspected")

    ov04x = {
        "observable_id": "OV-04x",
        "robustness_report_fingerprint": str(base.ov04x["robustness_report_fingerprint"]),
        "curved_adequacy_aggregation": str(base.ov04x.get("curved_adequacy_summary", {}).get("adequacy_aggregation", "unknown")),
        "curved_adequacy_summary": dict(base.ov04x.get("curved_adequacy_summary", {})),
        "suspicion_flags": ov04_flags,
        "windows": ov04_windows,
    }
    ov03x = {
        "observable_id": "OV-03x",
        "robustness_report_fingerprint": str(base.ov03x["robustness_report_fingerprint"]),
        "curved_adequacy_aggregation": str(base.ov03x.get("curved_adequacy_summary", {}).get("adequacy_aggregation", "unknown")),
        "curved_adequacy_summary": dict(base.ov03x.get("curved_adequacy_summary", {})),
        "suspicion_flags": [],
        "windows": ov03_windows,
    }

    return OVDQ01AdequacyDrilldownRecord(
        schema="OV-DQ-01_adequacy_drilldown/v1",
        adequacy_policy=str(adequacy_policy),
        ov04x=ov04x,
        ov03x=ov03x,
        notes=(
            "Window-level DQ-01 adequacy drilldown (metrics vs thresholds + ratios). "
            "Bookkeeping only; no policy mutation; no physics claim."
        ),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "diagnostics"
        / "OV-DQ-01"
        / "OV-DQ-01_adequacy_drilldown.json"
    )


def write_ovdq01_adequacy_drilldown_artifact(*, path: Path | None = None, adequacy_policy: str = "DQ-01_v1") -> Path:
    out = default_artifact_path() if path is None else Path(path)
    rec = ovdq01_adequacy_drilldown_record(adequacy_policy=str(adequacy_policy))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8")
    return out
