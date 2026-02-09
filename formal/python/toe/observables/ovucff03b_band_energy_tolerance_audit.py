"""OV-UCFF-03B: Band energy tolerance audit.

Purpose
- Turn OV-UCFF-03's deterministic spectral fingerprint into a revalidation check by
  comparing a newly computed OV-UCFF-03 report against a pinned reference report.

Policy / limits
- Bookkeeping only.
- Pass/fail is purely numeric consistency vs an internal pinned reference artifact.
- Reference artifacts are internal traceability anchors (not external evidence).

Notes
- The pinned reference is expected to be generated from the canonical OV-UCFF-03
  diagnostic artifact and then frozen.
"""

from __future__ import annotations

from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.toe.observables.ovucff03_band_energy_distribution_audit import (
    default_artifact_path as ovucff03_default_artifact_path,
    default_pinned_input_path as ovucff03_default_pinned_input_path,
    load_pinned_input_payload as ovucff03_load_pinned_input_payload,
    ovucff03_band_energy_distribution_audit,
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


def default_reference_report_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-03B"
        / "reference_ovucff03_pinned_report.json"
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "diagnostics"
        / "OV-UCFF-03B"
        / "ucff_band_energy_tolerance.json"
    )


def _rel_err(diff: np.ndarray, ref: np.ndarray, *, atol: float) -> np.ndarray:
    denom = np.maximum(np.abs(ref), float(atol))
    return np.abs(diff) / denom


def _as_float_array(x: Any) -> np.ndarray:
    if isinstance(x, list):
        return np.asarray(x, dtype=float)
    if isinstance(x, (tuple, np.ndarray)):
        return np.asarray(x, dtype=float)
    raise TypeError("expected list/tuple/ndarray")


@dataclass(frozen=True)
class OVUCFF03BToleranceCheckReport:
    schema: str
    notes: str
    rtol: float
    atol: float
    pass_all: bool
    comparisons: list[dict[str, Any]]
    current_report_schema: str
    current_report_fingerprint: str
    reference_report_schema: str
    reference_report_fingerprint: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def write_reference_report_from_ovucff03(
    *,
    path: Path | None = None,
    source_artifact_path: Path | None = None,
    report_key: str = "pinned",
) -> Path:
    """Write a frozen reference report extracted from the OV-UCFF-03 canonical artifact."""

    src = ovucff03_default_artifact_path() if source_artifact_path is None else Path(source_artifact_path)
    payload = json.loads(src.read_text(encoding="utf-8"))
    reports = payload.get("reports")
    if not isinstance(reports, dict):
        raise ValueError("OV-UCFF-03 artifact missing dict 'reports'")

    rep = reports.get(str(report_key))
    if rep is None:
        raise ValueError(f"OV-UCFF-03 artifact missing report key: {report_key!r}")
    if not isinstance(rep, dict):
        raise ValueError("OV-UCFF-03 artifact report is not a JSON object")

    out_payload: dict[str, Any] = {
        "schema": "OV-UCFF-03B/reference_report/v1",
        "notes": (
            "Pinned reference OV-UCFF-03 report used by OV-UCFF-03B for numeric tolerance revalidation. "
            "Internal traceability anchor only (not external evidence)."
        ),
        "source": {
            "schema": str(payload.get("schema")),
            "path": src.as_posix(),
            "fingerprint": str(payload.get("fingerprint")),
            "report_key": str(report_key),
        },
        "reference_report": rep,
    }
    out_payload["fingerprint"] = _sha256_json(out_payload)

    out = default_reference_report_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(out_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out


def load_reference_report(*, path: Path | None = None) -> dict[str, Any]:
    p = default_reference_report_path() if path is None else Path(path)
    payload = json.loads(p.read_text(encoding="utf-8"))
    if payload.get("schema") != "OV-UCFF-03B/reference_report/v1":
        raise ValueError("reference JSON schema mismatch")
    rep = payload.get("reference_report")
    if not isinstance(rep, dict):
        raise ValueError("reference JSON missing 'reference_report' object")
    return rep


def ovucff03b_tolerance_check(
    *,
    current_report: dict[str, Any],
    reference_report: dict[str, Any],
    rtol: float = 1e-6,
    atol: float = 1e-9,
) -> OVUCFF03BToleranceCheckReport:
    if rtol < 0 or atol < 0:
        raise ValueError("rtol and atol must be >= 0")

    fields_scalar = [
        "entropy_norm_mean",
        "flatness_mean",
        "energy_slope_mean",
    ]
    fields_vector = [
        "band_energy_norm_mean",
    ]

    comparisons: list[dict[str, Any]] = []
    pass_all = True

    def _cmp_scalar(name: str) -> None:
        nonlocal pass_all
        if name not in current_report or name not in reference_report:
            return
        a = float(current_report[name])
        b = float(reference_report[name])
        diff = float(a - b)
        abs_diff = float(abs(diff))
        rel = float(abs_diff / max(abs(b), float(atol)))
        ok = (abs_diff <= float(atol) + float(rtol) * abs(b))
        comparisons.append(
            {
                "field": name,
                "shape": [],
                "current": a,
                "reference": b,
                "abs_diff": abs_diff,
                "rel_err": rel,
                "pass": bool(ok),
            }
        )
        pass_all = pass_all and bool(ok)

    def _cmp_vector(name: str) -> None:
        nonlocal pass_all
        if name not in current_report or name not in reference_report:
            return
        a = _as_float_array(current_report[name]).ravel()
        b = _as_float_array(reference_report[name]).ravel()
        if a.shape != b.shape:
            comparisons.append(
                {
                    "field": name,
                    "shape": [int(v) for v in a.shape],
                    "reference_shape": [int(v) for v in b.shape],
                    "pass": False,
                    "reason": "shape_mismatch",
                }
            )
            pass_all = False
            return

        diff = a - b
        abs_diff = np.abs(diff)
        rel = _rel_err(diff, b, atol=float(atol))
        max_abs = float(np.max(abs_diff)) if abs_diff.size else 0.0
        max_rel = float(np.max(rel)) if rel.size else 0.0

        ok = bool(np.all(abs_diff <= float(atol) + float(rtol) * np.abs(b)))
        comparisons.append(
            {
                "field": name,
                "shape": [int(v) for v in a.shape],
                "max_abs_diff": max_abs,
                "max_rel_err": max_rel,
                "pass": bool(ok),
            }
        )
        pass_all = pass_all and bool(ok)

    for f in fields_scalar:
        _cmp_scalar(f)
    for f in fields_vector:
        _cmp_vector(f)

    # Compare legacy 3-band partition summaries if present in both.
    legacy_fields_scalar = [
        "legacy_k_low",
        "legacy_k_mid",
        "legacy_dx",
        "legacy_E_frac_low_mean",
        "legacy_E_frac_mid_mean",
        "legacy_E_frac_high_mean",
    ]
    if all((current_report.get(k) is not None and reference_report.get(k) is not None) for k in legacy_fields_scalar):
        for f in legacy_fields_scalar:
            _cmp_scalar(f)

    return OVUCFF03BToleranceCheckReport(
        schema="OV-UCFF-03B/tolerance_check_report/v1",
        notes=(
            "Numeric tolerance check between a freshly computed OV-UCFF-03 report and a pinned reference report. "
            "PASS/FAIL is purely internal consistency; not an external validation."
        ),
        rtol=float(rtol),
        atol=float(atol),
        pass_all=bool(pass_all),
        comparisons=comparisons,
        current_report_schema=str(current_report.get("schema")),
        current_report_fingerprint=str(current_report.get("fingerprint")),
        reference_report_schema=str(reference_report.get("schema")),
        reference_report_fingerprint=str(reference_report.get("fingerprint")),
    )


def write_ovucff03b_band_energy_tolerance_artifact(
    *,
    path: Path | None = None,
    reference_path: Path | None = None,
    rtol: float = 1e-6,
    atol: float = 1e-9,
    n_bands: int = 8,
    eps: float = 1e-12,
    legacy_k_low: float = 2.0,
    legacy_k_mid: float = 6.0,
) -> Path:
    ref_path = default_reference_report_path() if reference_path is None else Path(reference_path)
    if not ref_path.exists():
        # Conservative default: write reference from the current canonical OV-UCFF-03 artifact.
        write_reference_report_from_ovucff03(path=ref_path)

    ref_report = load_reference_report(path=ref_path)

    pinned_payload = ovucff03_load_pinned_input_payload(path=ovucff03_default_pinned_input_path())
    Xp = pinned_payload["X"]
    dxp = pinned_payload["dx"]

    current = ovucff03_band_energy_distribution_audit(
        X=Xp,
        n_bands=int(n_bands),
        eps=float(eps),
        dx=dxp,
        legacy_k_low=float(legacy_k_low),
        legacy_k_mid=float(legacy_k_mid),
    ).to_jsonable()

    check = ovucff03b_tolerance_check(
        current_report=current,
        reference_report=ref_report,
        rtol=float(rtol),
        atol=float(atol),
    ).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-03B/band_energy_tolerance_artifact/v1",
        "notes": (
            "Bookkeeping only. Computes OV-UCFF-03 on the pinned internal input and compares it to a pinned reference "
            "OV-UCFF-03 report under numeric tolerances, emitting PASS/FAIL and error summaries. Not external evidence."
        ),
        "ovucff03_source_artifact": {
            "path": ovucff03_default_artifact_path().as_posix(),
        },
        "pinned_input": {
            "path": ovucff03_default_pinned_input_path().as_posix(),
            "schema": "OV-UCFF-03/pinned_input_density_pair/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
            "dx": dxp,
        },
        "reference": {
            "path": ref_path.as_posix(),
            "schema": "OV-UCFF-03B/reference_report/v1",
        },
        "params": {
            "rtol": float(rtol),
            "atol": float(atol),
            "n_bands": int(n_bands),
            "eps": float(eps),
            "legacy_k_low": float(legacy_k_low),
            "legacy_k_mid": float(legacy_k_mid),
        },
        "current_report": current,
        "tolerance_check": check,
    }

    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
