from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from formal.python.toe.ucff.core_front_door import UcffCoreReport


CV03_TOLERANCE_PROFILE_ENV = "TOE_CV03_TOLERANCE_PROFILE"

CV03_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "rel_l2_mismatch": 1e-12,
        "max_relative_error": 1e-12,
        "relative_floor": 1e-12,
        "nonnegative_floor": -1e-14,
        "monotonicity_eps": 1e-12,
    },
    "portable": {
        "rel_l2_mismatch": 1e-9,
        "max_relative_error": 1e-9,
        "relative_floor": 1e-9,
        "nonnegative_floor": -1e-9,
        "monotonicity_eps": 1e-9,
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
    return repo_root / "formal" / "external_evidence" / "ucff_dispersion_comparator_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_ucff_report_artifact(path: Path) -> tuple[UcffCoreReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "UCFF/core_front_door_report/v1":
        raise ValueError(f"Unexpected UCFF core report schema in {path}: {payload.get('schema')!r}")

    report = UcffCoreReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        params={
            "rho0": float(payload["params"]["rho0"]),
            "g": float(payload["params"]["g"]),
            "lam": float(payload["params"]["lam"]),
            "beta": float(payload["params"]["beta"]),
        },
        k=[float(x) for x in payload["k"]],
        omega2=[float(x) for x in payload["omega2"]],
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def cv03_v1_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CV03_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CV03_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CV03_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CV03_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def cv03_v1_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CV03_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CV03_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CV03_TOLERANCE_PROFILES[p])


def _is_nondecreasing(values: np.ndarray, *, eps: float) -> bool:
    if values.size <= 1:
        return True
    return bool(np.all(np.diff(values) >= -float(eps)))


def cv03_compare_dispersion_surfaces(
    reference: UcffCoreReport,
    candidate: UcffCoreReport,
    *,
    tolerances: Mapping[str, float],
    enforce_monotonicity: bool = True,
    deterministic_ok: bool = True,
) -> dict[str, Any]:
    if not isinstance(reference, UcffCoreReport):
        raise TypeError("reference must be a UcffCoreReport")
    if not isinstance(candidate, UcffCoreReport):
        raise TypeError("candidate must be a UcffCoreReport")

    ref_k = np.asarray(reference.k, dtype=float)
    ref_omega2 = np.asarray(reference.omega2, dtype=float)
    cand_k = np.asarray(candidate.k, dtype=float)
    cand_omega2 = np.asarray(candidate.omega2, dtype=float)

    order_ref = _is_nondecreasing(ref_k, eps=float(tolerances["monotonicity_eps"]))
    order_cand = _is_nondecreasing(cand_k, eps=float(tolerances["monotonicity_eps"]))
    aligned = bool(ref_k.shape == cand_k.shape and np.array_equal(ref_k, cand_k))

    rel_l2_mismatch: float | None = None
    max_relative_error: float | None = None
    min_candidate_omega2: float | None = None
    monotonicity_ok: bool | None = None

    reasons: list[str] = []
    if not order_ref or not order_cand:
        reasons.append("FAIL_K_GRID_ORDER")
    if not aligned:
        reasons.append("FAIL_K_GRID_ALIGNMENT")
    if not bool(deterministic_ok):
        reasons.append("FAIL_DISPERSION_NONDETERMINISTIC")

    if aligned and ref_omega2.shape == cand_omega2.shape:
        delta = np.abs(cand_omega2 - ref_omega2)
        denom = np.maximum(np.abs(ref_omega2), float(tolerances["relative_floor"]))
        rel = delta / denom

        rel_l2_mismatch = float(np.linalg.norm(delta) / max(float(np.linalg.norm(ref_omega2)), float(tolerances["relative_floor"])))
        max_relative_error = float(np.max(rel)) if rel.size > 0 else 0.0
        min_candidate_omega2 = float(np.min(cand_omega2)) if cand_omega2.size > 0 else 0.0
        monotonicity_ok = _is_nondecreasing(cand_omega2, eps=float(tolerances["monotonicity_eps"]))

        if min_candidate_omega2 < float(tolerances["nonnegative_floor"]):
            reasons.append("FAIL_DISPERSION_SIGN")
        if bool(enforce_monotonicity) and not monotonicity_ok:
            reasons.append("FAIL_DISPERSION_MONOTONICITY")
        if (
            rel_l2_mismatch > float(tolerances["rel_l2_mismatch"])
            or max_relative_error > float(tolerances["max_relative_error"])
        ):
            reasons.append("FAIL_DISPERSION_SHAPE_MISMATCH")

    if reasons:
        passed = False
    else:
        passed = True
        reasons = ["cv03_dispersion_constraints_satisfied"]

    return {
        "artifact_id": "UCFF_DISPERSION",
        "source": {
            "reference_schema": reference.schema,
            "candidate_schema": candidate.schema,
            "reference_config_tag": reference.config_tag,
            "candidate_config_tag": candidate.config_tag,
        },
        "input_fingerprint": candidate.fingerprint(),
        "input_data_fingerprint": candidate.fingerprint(),
        "metric_vector": {
            "rel_l2_mismatch": rel_l2_mismatch,
            "max_relative_error": max_relative_error,
        },
        "passed": bool(passed),
        "reason_codes": list(reasons),
        "diagnostics": {
            "reference_fingerprint": reference.fingerprint(),
            "candidate_fingerprint": candidate.fingerprint(),
            "k_count_reference": int(ref_k.size),
            "k_count_candidate": int(cand_k.size),
            "k_grid_order_reference": bool(order_ref),
            "k_grid_order_candidate": bool(order_cand),
            "k_grid_aligned": bool(aligned),
            "min_candidate_omega2": min_candidate_omega2,
            "enforce_monotonicity": bool(enforce_monotonicity),
            "candidate_monotonic_non_decreasing": monotonicity_ok,
        },
    }


@dataclass(frozen=True)
class CV03UcffDispersionV1Record:
    schema: str
    date: str
    observable_id: str
    domain_id: str
    comparator_role: str
    tolerance_profile: str
    status: dict[str, Any]
    inputs: dict[str, Any]
    rows: list[dict[str, Any]]
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
            "summary": dict(self.summary),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def cv03_ucff_dispersion_v1_record(
    *,
    date: str = "2026-02-08",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CV03UcffDispersionV1Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else cv03_v1_tolerance_profile_from_env(env)
    tolerances = cv03_v1_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "cv03_reference_ucff_core_report.json"
    cand_path = data_dir / "cv03_candidate_ucff_core_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return CV03UcffDispersionV1Record(
            schema="OV-CV-03_ucff_dispersion_comparator/v1",
            date=str(date),
            observable_id="OV-CV-03",
            domain_id="DRBR-DOMAIN-UCFF-01",
            comparator_role="discriminative_candidate",
            tolerance_profile=profile,
            status={"blocked": True, "reasons": ["missing_domain_artifacts"]},
            inputs={"artifact_dir": str(data_dir), "missing_artifacts": list(missing)},
            rows=[],
            summary={"counts": {"pass": 0, "fail": 0}, "artifacts": {"pass": [], "fail": []}},
            scope_limits=["blocked_by_missing_inputs", "front_door_only"],
        )

    ref_report, ref_fp_ok = _load_ucff_report_artifact(ref_path)
    cand_report, cand_fp_ok = _load_ucff_report_artifact(cand_path)

    row = cv03_compare_dispersion_surfaces(
        ref_report,
        cand_report,
        tolerances=tolerances,
        enforce_monotonicity=True,
        deterministic_ok=bool(ref_fp_ok and cand_fp_ok),
    )
    pass_ids = [str(row["artifact_id"])] if bool(row["passed"]) else []
    fail_ids = [str(row["artifact_id"])] if not bool(row["passed"]) else []

    return CV03UcffDispersionV1Record(
        schema="OV-CV-03_ucff_dispersion_comparator/v1",
        date=str(date),
        observable_id="OV-CV-03",
        domain_id="DRBR-DOMAIN-UCFF-01",
        comparator_role="discriminative_candidate",
        tolerance_profile=profile,
        status={
            "blocked": False,
            "reasons": [],
            "fingerprint_checks": {"reference_report": bool(ref_fp_ok), "candidate_report": bool(cand_fp_ok)},
            "tolerances": dict(tolerances),
        },
        inputs={
            "artifact_dir": str(data_dir),
            "reference_artifact_path": str(ref_path),
            "candidate_artifact_path": str(cand_path),
            "reference_fingerprint": ref_report.fingerprint(),
            "candidate_fingerprint": cand_report.fingerprint(),
        },
        rows=[row],
        summary={"counts": {"pass": len(pass_ids), "fail": len(fail_ids)}, "artifacts": {"pass": pass_ids, "fail": fail_ids}},
        scope_limits=[
            "front_door_only",
            "typed_artifacts_only",
            "deterministic_record_only",
            "discriminative_candidate",
            "no_external_truth_claim",
        ],
    )


def render_cv03_lock_markdown(record: CV03UcffDispersionV1Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-CV-03 - UCFF Dispersion Comparator v1 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted UCFF core report artifacts only\n"
        "- Explicit failure reason taxonomy for grid/sign/shape/monotonicity/determinism\n"
        "- No external truth claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
