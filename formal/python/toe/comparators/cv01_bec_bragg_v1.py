from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

from formal.python.toe.comparators.cv01_bec_bragg_v0 import (
    cv01_compare_curved_fit,
    cv01_compare_linear_fit,
)
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D


CV01_TOLERANCE_PROFILE_ENV = "TOE_CV01_TOLERANCE_PROFILE"

CV01_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "metric_identity": 1e-12,
        "unit_gxx": 1e-12,
        "declared_speed_match": 1e-12,
        "cross_artifact_speed": 2e-4,
    },
    "portable": {
        "metric_identity": 1e-10,
        "unit_gxx": 1e-10,
        "declared_speed_match": 1e-10,
        "cross_artifact_speed": 5e-4,
    },
}


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


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _as_sample_kw(raw_sample_kw: list[list[float]]) -> tuple[tuple[float, float], ...]:
    return tuple((float(k), float(w)) for (k, w) in raw_sample_kw)


def _load_dr01_linear(path: Path) -> DR01Fit1D:
    payload = _load_json(path)
    return DR01Fit1D(
        u=float(payload["u"]),
        c_s=float(payload["c_s"]),
        tag=str(payload.get("tag", "dr01_linear_artifact")),
        source_kind=str(payload.get("source_kind", "unknown")),
        source_ref=str(payload.get("source_ref", "unknown")),
        fit_method_tag=str(payload.get("fit_method_tag", "unspecified")),
        sample_kw=_as_sample_kw(payload["sample_kw"]),
        data_fingerprint=str(payload.get("data_fingerprint", "")),
    )


def _load_dr01_curved(path: Path) -> DR01FitCurved1D:
    payload = _load_json(path)
    return DR01FitCurved1D(
        u=float(payload["u"]),
        c0=float(payload["c0"]),
        beta=float(payload["beta"]),
        tag=str(payload.get("tag", "dr01_curved_artifact")),
        source_kind=str(payload.get("source_kind", "unknown")),
        source_ref=str(payload.get("source_ref", "unknown")),
        fit_method_tag=str(payload.get("fit_method_tag", "unspecified")),
        sample_kw=_as_sample_kw(payload["sample_kw"]),
        data_fingerprint=str(payload.get("data_fingerprint", "")),
    )


def cv01_v1_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CV01_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CV01_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CV01_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CV01_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def cv01_v1_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CV01_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CV01_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CV01_TOLERANCE_PROFILES[p])


def cv01_v1_compare_linear_fit(
    dr01_fit: DR01Fit1D,
    *,
    tolerances: Mapping[str, float],
) -> dict[str, Any]:
    return cv01_compare_linear_fit(
        dr01_fit,
        tol_metric_identity=float(tolerances["metric_identity"]),
        tol_unit_gxx=float(tolerances["unit_gxx"]),
        tol_declared_speed=float(tolerances["declared_speed_match"]),
    )


def cv01_v1_compare_curved_fit(
    dr01_fit_curved: DR01FitCurved1D,
    *,
    tolerances: Mapping[str, float],
) -> dict[str, Any]:
    return cv01_compare_curved_fit(
        dr01_fit_curved,
        tol_metric_identity=float(tolerances["metric_identity"]),
        tol_unit_gxx=float(tolerances["unit_gxx"]),
        tol_declared_speed=float(tolerances["declared_speed_match"]),
    )


def cv01_v1_cross_artifact_speed_residual(
    dr01_linear: DR01Fit1D,
    dr01_curved: DR01FitCurved1D,
    *,
    tol_cross_artifact: float,
) -> dict[str, Any]:
    linear_speed = float(dr01_linear.c_s)
    curved_speed = float(dr01_curved.c0)
    residual = abs(linear_speed - curved_speed)

    reasons: list[str] = []
    passed = True
    if linear_speed <= 0.0 or curved_speed <= 0.0:
        passed = False
        reasons.append("cv01_fail_cross_artifact_nonpositive_speed")
    elif residual > float(tol_cross_artifact):
        passed = False
        reasons.append("cv01_fail_linear_vs_curved_speed_inconsistent")
    else:
        reasons.append("cv01_v1_cross_artifact_speed_consistent")

    return {
        "check_id": "linear_vs_curved_speed_residual",
        "input_fingerprints": {
            "linear": dr01_linear.fingerprint(),
            "curved": dr01_curved.fingerprint(),
        },
        "input_data_fingerprints": {
            "linear": dr01_linear.data_fingerprint,
            "curved": dr01_curved.data_fingerprint,
        },
        "speed_linear": linear_speed,
        "speed_curved": curved_speed,
        "speed_residual": float(residual),
        "tolerance": float(tol_cross_artifact),
        "passed": bool(passed),
        "reason_codes": list(reasons),
    }


@dataclass(frozen=True)
class CV01BecBraggV1Record:
    schema: str
    date: str
    observable_id: str
    domain_id: str
    comparator_role: str
    tolerance_profile: str
    status: dict[str, Any]
    inputs: dict[str, Any]
    rows: list[dict[str, Any]]
    cross_artifact: dict[str, Any]
    summary: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "domain_id": str(self.domain_id),
            "comparator_role": str(self.comparator_role),
            "tolerance_profile": str(self.tolerance_profile),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "rows": list(self.rows),
            "cross_artifact": dict(self.cross_artifact),
            "summary": dict(self.summary),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def cv01_bec_bragg_v1_record(
    *,
    date: str = "2026-02-08",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CV01BecBraggV1Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else cv01_v1_tolerance_profile_from_env(env)
    tolerances = cv01_v1_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    linear_path = data_dir / "dr01_fit_artifact.json"
    curved_path = data_dir / "dr01_fit_artifact_curved.json"

    missing = [str(p) for p in [linear_path, curved_path] if not p.exists()]
    if missing:
        return CV01BecBraggV1Record(
            schema="OV-CV-01_bec_bragg_v1_comparator/v1",
            date=str(date),
            observable_id="OV-CV-01",
            domain_id="DRBR-DOMAIN-01",
            comparator_role="discriminative_candidate",
            tolerance_profile=profile,
            status={
                "blocked": True,
                "reasons": ["missing_domain_artifacts"],
            },
            inputs={
                "artifact_dir": str(data_dir),
                "missing_artifacts": list(missing),
            },
            rows=[],
            cross_artifact={
                "check_id": "linear_vs_curved_speed_residual",
                "input_fingerprints": {
                    "linear": "",
                    "curved": "",
                },
                "input_data_fingerprints": {
                    "linear": None,
                    "curved": None,
                },
                "speed_linear": None,
                "speed_curved": None,
                "speed_residual": None,
                "tolerance": float(tolerances["cross_artifact_speed"]),
                "passed": False,
                "reason_codes": ["cv01_fail_cross_artifact_missing_inputs"],
            },
            summary={
                "rows": {"pass": 0, "fail": 0},
                "cross_artifact": {"pass": 0, "fail": 1},
                "artifacts": {"pass": [], "fail": []},
            },
            scope_limits=["blocked_by_missing_inputs", "front_door_only"],
        )

    fit_linear = _load_dr01_linear(linear_path)
    fit_curved = _load_dr01_curved(curved_path)

    row_linear = cv01_v1_compare_linear_fit(fit_linear, tolerances=tolerances)
    row_curved = cv01_v1_compare_curved_fit(fit_curved, tolerances=tolerances)
    cross = cv01_v1_cross_artifact_speed_residual(
        fit_linear,
        fit_curved,
        tol_cross_artifact=float(tolerances["cross_artifact_speed"]),
    )

    rows = [row_linear, row_curved]
    pass_ids = [str(r["artifact_id"]) for r in rows if bool(r["passed"])]
    fail_ids = [str(r["artifact_id"]) for r in rows if not bool(r["passed"])]

    return CV01BecBraggV1Record(
        schema="OV-CV-01_bec_bragg_v1_comparator/v1",
        date=str(date),
        observable_id="OV-CV-01",
        domain_id="DRBR-DOMAIN-01",
        comparator_role="discriminative_candidate",
        tolerance_profile=profile,
        status={
            "blocked": False,
            "reasons": [],
            "tolerances": {
                "metric_identity": float(tolerances["metric_identity"]),
                "unit_gxx": float(tolerances["unit_gxx"]),
                "declared_speed_match": float(tolerances["declared_speed_match"]),
                "cross_artifact_speed": float(tolerances["cross_artifact_speed"]),
            },
        },
        inputs={
            "artifact_dir": str(data_dir),
            "linear_artifact_path": str(linear_path),
            "curved_artifact_path": str(curved_path),
            "linear_data_fingerprint": fit_linear.data_fingerprint,
            "curved_data_fingerprint": fit_curved.data_fingerprint,
        },
        rows=rows,
        cross_artifact=cross,
        summary={
            "rows": {"pass": len(pass_ids), "fail": len(fail_ids)},
            "cross_artifact": {"pass": 1 if bool(cross["passed"]) else 0, "fail": 0 if bool(cross["passed"]) else 1},
            "artifacts": {"pass": pass_ids, "fail": fail_ids},
        },
        scope_limits=[
            "front_door_only",
            "typed_artifacts_only",
            "deterministic_record_only",
            "discriminative_candidate",
            "no_external_truth_claim",
        ],
    )


def render_cv01_v1_lock_markdown(record: CV01BecBraggV1Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-CV-01 — BEC Bragg Comparator v1 (cross-artifact, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed DR-01 artifacts only (linear + curved)\n"
        "- Includes non-tautological cross-artifact speed residual check\n"
        "- No external truth claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
