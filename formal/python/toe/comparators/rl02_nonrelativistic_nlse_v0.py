from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np


RL02_TOLERANCE_PROFILE_ENV = "TOE_RL02_TOLERANCE_PROFILE"

RL02_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "rel_l2_mismatch": 1e-12,
        "max_relative_error": 1e-12,
        "relative_floor": 1e-12,
        "scaling_abs_tol": 1e-12,
        "monotonicity_eps": 1e-12,
    },
    "portable": {
        "rel_l2_mismatch": 1e-9,
        "max_relative_error": 1e-9,
        "relative_floor": 1e-9,
        "scaling_abs_tol": 1e-9,
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


def _relpath(repo_root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return str(path)


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "rl02_nonrelativistic_limit_nlse_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class RL02NLSEReport:
    schema: str
    config_tag: str
    regime_tag: str
    params: dict[str, float]
    k: list[float]
    omega: list[float]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "params": dict(self.params),
            "k": list(self.k),
            "omega": list(self.omega),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_rl02_report_artifact(path: Path) -> tuple[RL02NLSEReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "RL/nr_nlse_front_door_report/v1":
        raise ValueError(f"Unexpected RL02 report schema in {path}: {payload.get('schema')!r}")

    report = RL02NLSEReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        params={
            "m": float(payload["params"]["m"]),
            "mu": float(payload["params"]["mu"]),
            "epsilon": float(payload["params"]["epsilon"]),
        },
        k=[float(x) for x in payload["k"]],
        omega=[float(x) for x in payload["omega"]],
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def rl02_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(RL02_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in RL02_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL02_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {RL02_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def rl02_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in RL02_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL02_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(RL02_TOLERANCE_PROFILES[p])


def _is_nondecreasing(values: np.ndarray, *, eps: float) -> bool:
    if values.size <= 1:
        return True
    return bool(np.all(np.diff(values) >= -float(eps)))


def _expected_nr_omega(*, k: np.ndarray, m: float, mu: float) -> np.ndarray:
    return (k * k) / (2.0 * float(m)) + float(mu)


def rl02_compare_surfaces(
    reference: RL02NLSEReport,
    candidate: RL02NLSEReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> dict[str, Any]:
    if not isinstance(reference, RL02NLSEReport):
        raise TypeError("reference must be a RL02NLSEReport")
    if not isinstance(candidate, RL02NLSEReport):
        raise TypeError("candidate must be a RL02NLSEReport")

    ref_k = np.asarray(reference.k, dtype=float)
    ref_omega = np.asarray(reference.omega, dtype=float)
    cand_k = np.asarray(candidate.k, dtype=float)
    cand_omega = np.asarray(candidate.omega, dtype=float)

    order_ref = _is_nondecreasing(ref_k, eps=float(tolerances["monotonicity_eps"]))
    order_cand = _is_nondecreasing(cand_k, eps=float(tolerances["monotonicity_eps"]))
    aligned = bool(ref_k.shape == cand_k.shape and np.array_equal(ref_k, cand_k))

    rel_l2_mismatch: float | None = None
    max_relative_error: float | None = None
    scaling_max_abs_reference: float | None = None
    scaling_max_abs_candidate: float | None = None

    reasons: list[str] = []
    if reference.regime_tag != candidate.regime_tag:
        reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
    if reference.params != candidate.params:
        reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
    if not order_ref or not order_cand:
        reasons.append("FAIL_K_GRID_ORDER")
    if not aligned:
        reasons.append("FAIL_K_GRID_ALIGNMENT")
    if not bool(deterministic_ok):
        reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

    if aligned and ref_omega.shape == cand_omega.shape:
        delta = np.abs(cand_omega - ref_omega)
        denom = np.maximum(np.abs(ref_omega), float(tolerances["relative_floor"]))
        rel = delta / denom

        rel_l2_mismatch = float(np.linalg.norm(delta) / max(float(np.linalg.norm(ref_omega)), float(tolerances["relative_floor"])))
        max_relative_error = float(np.max(rel)) if rel.size > 0 else 0.0

        expected_ref = _expected_nr_omega(k=ref_k, m=reference.params["m"], mu=reference.params["mu"])
        expected_cand = _expected_nr_omega(k=cand_k, m=candidate.params["m"], mu=candidate.params["mu"])
        scaling_max_abs_reference = float(np.max(np.abs(ref_omega - expected_ref))) if ref_omega.size > 0 else 0.0
        scaling_max_abs_candidate = float(np.max(np.abs(cand_omega - expected_cand))) if cand_omega.size > 0 else 0.0

        if scaling_max_abs_reference > float(tolerances["scaling_abs_tol"]):
            reasons.append("FAIL_LIMIT_SCALING_MISMATCH")
        if scaling_max_abs_candidate > float(tolerances["scaling_abs_tol"]):
            reasons.append("FAIL_LIMIT_SCALING_MISMATCH")
        if (
            rel_l2_mismatch > float(tolerances["rel_l2_mismatch"])
            or max_relative_error > float(tolerances["max_relative_error"])
        ):
            reasons.append("FAIL_DISPERSION_MISMATCH")

    if reasons:
        passed = False
    else:
        passed = True
        reasons = ["rl02_nonrelativistic_limit_constraints_satisfied"]

    return {
        "artifact_id": "RL02_NR_NLSE_LIMIT",
        "source": {
            "reference_schema": reference.schema,
            "candidate_schema": candidate.schema,
            "reference_config_tag": reference.config_tag,
            "candidate_config_tag": candidate.config_tag,
            "reference_regime_tag": reference.regime_tag,
            "candidate_regime_tag": candidate.regime_tag,
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
            "scaling_max_abs_reference": scaling_max_abs_reference,
            "scaling_max_abs_candidate": scaling_max_abs_candidate,
        },
    }


@dataclass(frozen=True)
class RL02NonrelativisticNlseV0Record:
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
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def rl02_nonrelativistic_nlse_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> RL02NonrelativisticNlseV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else rl02_v0_tolerance_profile_from_env(env)
    tolerances = rl02_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "rl02_reference_report.json"
    cand_path = data_dir / "rl02_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return RL02NonrelativisticNlseV0Record(
            schema="OV-RL-02_nonrelativistic_nlse_comparator/v0",
            date=str(date),
            observable_id="OV-RL-02",
            domain_id="DRBR-DOMAIN-RL-02",
            comparator_role="discriminative_candidate",
            tolerance_profile=profile,
            status={"blocked": True, "reasons": ["missing_domain_artifacts"]},
            inputs={
                "artifact_dir": _relpath(repo_root, data_dir),
                "missing_artifacts": [_relpath(repo_root, Path(p)) for p in missing],
            },
            rows=[],
            summary={"counts": {"pass": 0, "fail": 0}, "artifacts": {"pass": [], "fail": []}},
            scope_limits=["blocked_by_missing_inputs", "front_door_only"],
        )

    reference, ref_deterministic = _load_rl02_report_artifact(ref_path)
    candidate, cand_deterministic = _load_rl02_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    row = rl02_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in [row] if r["passed"]]
    failed = [r for r in [row] if not r["passed"]]

    return RL02NonrelativisticNlseV0Record(
        schema="OV-RL-02_nonrelativistic_nlse_comparator/v0",
        date=str(date),
        observable_id="OV-RL-02",
        domain_id="DRBR-DOMAIN-RL-02",
        comparator_role="discriminative_candidate",
        tolerance_profile=profile,
        status={"blocked": False, "reasons": []},
        inputs={
            "artifact_dir": _relpath(repo_root, data_dir),
            "reference_artifact": _relpath(repo_root, ref_path),
            "candidate_artifact": _relpath(repo_root, cand_path),
        },
        rows=[row],
        summary={
            "counts": {"pass": len(passed), "fail": len(failed)},
            "artifacts": {
                "pass": [r["artifact_id"] for r in passed],
                "fail": [r["artifact_id"] for r in failed],
            },
        },
        scope_limits=[
            "front_door_only",
            "typed_artifacts_only",
            "deterministic_record_only",
            "discriminative_candidate",
            "within_rep_only",
            "no_external_truth_claim",
        ],
    )


def render_rl02_lock_markdown(record: RL02NonrelativisticNlseV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-RL-02 - Nonrelativistic NLSE Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted RL02 report artifacts only\n"
        "- Explicit failure reason taxonomy for grid/limit/dispersion/determinism\n"
        "- No external truth claim\n\n"
        "Reproduce\n"
        "- Run: `.\\py.ps1 -m formal.python.tools.rl02_nonrelativistic_nlse_front_door; "
        ".\\py.ps1 -m pytest formal/python/tests/test_rl02_nonrelativistic_nlse_v0_lock.py`\n"
        "- Expected artifacts: `formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_reference_report.json`, "
        "`formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_candidate_report.json`\n"
        "- Lock fingerprint must match the value below.\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
