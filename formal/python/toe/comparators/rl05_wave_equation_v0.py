from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np


RL05_TOLERANCE_PROFILE_ENV = "TOE_RL05_TOLERANCE_PROFILE"

RL05_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "residual_l2_ratio": 1e-8,
        "residual_linf_abs": 1e-8,
        "relative_floor": 1e-12,
        "grid_order_eps": 1e-12,
    },
    "portable": {
        "residual_l2_ratio": 1e-6,
        "residual_linf_abs": 1e-6,
        "relative_floor": 1e-9,
        "grid_order_eps": 1e-9,
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
    return repo_root / "formal" / "external_evidence" / "rl05_wave_equation_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class RL05WaveEquationReport:
    schema: str
    config_tag: str
    regime_tag: str
    params: dict[str, float]
    boundary: str
    t: list[float]
    x: list[float]
    u: list[list[float]]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "params": dict(self.params),
            "boundary": str(self.boundary),
            "t": list(self.t),
            "x": list(self.x),
            "u": [list(row) for row in self.u],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_rl05_report_artifact(path: Path) -> tuple[RL05WaveEquationReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "RL/wave_equation_front_door_report/v1":
        raise ValueError(f"Unexpected RL05 report schema in {path}: {payload.get('schema')!r}")

    report = RL05WaveEquationReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        params={
            "length": float(payload["params"]["length"]),
            "nx": float(payload["params"]["nx"]),
            "dt": float(payload["params"]["dt"]),
            "nt": float(payload["params"]["nt"]),
            "c": float(payload["params"]["c"]),
            "k": float(payload["params"]["k"]),
            "amplitude": float(payload["params"]["amplitude"]),
        },
        boundary=str(payload["boundary"]),
        t=[float(v) for v in payload["t"]],
        x=[float(v) for v in payload["x"]],
        u=[[float(v) for v in row] for row in payload["u"]],
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def rl05_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(RL05_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in RL05_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL05_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {RL05_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def rl05_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in RL05_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL05_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(RL05_TOLERANCE_PROFILES[p])


def _is_nondecreasing(values: np.ndarray, *, eps: float) -> bool:
    if values.size <= 1:
        return True
    return bool(np.all(np.diff(values) >= -float(eps)))


def _d2x_periodic(values: np.ndarray, *, dx: float) -> np.ndarray:
    return (np.roll(values, -1, axis=-1) - 2.0 * values + np.roll(values, 1, axis=-1)) / float(dx * dx)


def rl05_compare_surfaces(
    reference: RL05WaveEquationReport,
    candidate: RL05WaveEquationReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> dict[str, Any]:
    if not isinstance(reference, RL05WaveEquationReport):
        raise TypeError("reference must be a RL05WaveEquationReport")
    if not isinstance(candidate, RL05WaveEquationReport):
        raise TypeError("candidate must be a RL05WaveEquationReport")

    ref_t = np.asarray(reference.t, dtype=float)
    ref_x = np.asarray(reference.x, dtype=float)
    cand_t = np.asarray(candidate.t, dtype=float)
    cand_x = np.asarray(candidate.x, dtype=float)

    order_t_ref = _is_nondecreasing(ref_t, eps=float(tolerances["grid_order_eps"]))
    order_x_ref = _is_nondecreasing(ref_x, eps=float(tolerances["grid_order_eps"]))
    order_t_cand = _is_nondecreasing(cand_t, eps=float(tolerances["grid_order_eps"]))
    order_x_cand = _is_nondecreasing(cand_x, eps=float(tolerances["grid_order_eps"]))
    aligned_t = bool(ref_t.shape == cand_t.shape and np.array_equal(ref_t, cand_t))
    aligned_x = bool(ref_x.shape == cand_x.shape and np.array_equal(ref_x, cand_x))

    residual_l2_ratio: float | None = None
    residual_linf_abs: float | None = None

    reasons: list[str] = []
    if reference.regime_tag != candidate.regime_tag:
        reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
    if reference.params != candidate.params:
        reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
    if reference.boundary != candidate.boundary:
        reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
    if not order_t_ref or not order_t_cand:
        reasons.append("FAIL_T_GRID_ORDER")
    if not order_x_ref or not order_x_cand:
        reasons.append("FAIL_X_GRID_ORDER")
    if not aligned_t:
        reasons.append("FAIL_T_GRID_ALIGNMENT")
    if not aligned_x:
        reasons.append("FAIL_X_GRID_ALIGNMENT")
    if not bool(deterministic_ok):
        reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

    u = np.asarray(candidate.u, dtype=float)
    if aligned_t and aligned_x and u.shape[0] >= 3:
        length = float(candidate.params["length"])
        nx = int(round(float(candidate.params["nx"])))
        dt = float(candidate.params["dt"])
        c = float(candidate.params["c"])
        dx = float(length) / float(nx)

        d2u_dt2 = (u[2:, :] - 2.0 * u[1:-1, :] + u[:-2, :]) / float(dt * dt)
        d2u_dx2 = _d2x_periodic(u[1:-1, :], dx=dx)
        residual = d2u_dt2 - (c * c) * d2u_dx2
        denom = max(float(np.linalg.norm((c * c) * d2u_dx2)), float(tolerances["relative_floor"]))
        residual_l2_ratio = float(np.linalg.norm(residual) / denom)
        residual_linf_abs = float(np.max(np.abs(residual))) if residual.size > 0 else 0.0

        if residual_l2_ratio > float(tolerances["residual_l2_ratio"]) or residual_linf_abs > float(
            tolerances["residual_linf_abs"]
        ):
            reasons.append("FAIL_WAVE_RESIDUAL")

    if reasons:
        passed = False
    else:
        passed = True
        reasons = ["rl05_wave_equation_constraints_satisfied"]

    return {
        "artifact_id": "RL05_WAVE_EQUATION",
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
            "residual_l2_ratio": residual_l2_ratio,
            "residual_linf_abs": residual_linf_abs,
        },
        "passed": bool(passed),
        "reason_codes": list(reasons),
        "diagnostics": {
            "reference_fingerprint": reference.fingerprint(),
            "candidate_fingerprint": candidate.fingerprint(),
            "t_count_reference": int(ref_t.size),
            "t_count_candidate": int(cand_t.size),
            "x_count_reference": int(ref_x.size),
            "x_count_candidate": int(cand_x.size),
            "t_grid_order_reference": bool(order_t_ref),
            "t_grid_order_candidate": bool(order_t_cand),
            "x_grid_order_reference": bool(order_x_ref),
            "x_grid_order_candidate": bool(order_x_cand),
            "t_grid_aligned": bool(aligned_t),
            "x_grid_aligned": bool(aligned_x),
        },
    }


@dataclass(frozen=True)
class RL05WaveEquationV0Record:
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


def rl05_wave_equation_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> RL05WaveEquationV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else rl05_v0_tolerance_profile_from_env(env)
    tolerances = rl05_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "rl05_reference_report.json"
    cand_path = data_dir / "rl05_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return RL05WaveEquationV0Record(
            schema="OV-RL-05_wave_equation_comparator/v0",
            date=str(date),
            observable_id="OV-RL-05",
            domain_id="DRBR-DOMAIN-RL-05",
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

    reference, ref_deterministic = _load_rl05_report_artifact(ref_path)
    candidate, cand_deterministic = _load_rl05_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    row = rl05_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in [row] if r["passed"]]
    failed = [r for r in [row] if not r["passed"]]

    return RL05WaveEquationV0Record(
        schema="OV-RL-05_wave_equation_comparator/v0",
        date=str(date),
        observable_id="OV-RL-05",
        domain_id="DRBR-DOMAIN-RL-05",
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


def render_rl05_lock_markdown(record: RL05WaveEquationV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-RL-05 - Wave Equation Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted RL05 report artifacts only\n"
        "- Explicit failure reason taxonomy for grid/wave residual/determinism\n"
        "- No external truth claim\n\n"
        "Reproduce\n"
        "- Run: `.\\py.ps1 -m formal.python.tools.rl05_wave_equation_front_door; "
        ".\\py.ps1 -m pytest formal/python/tests/test_rl05_wave_equation_v0_lock.py`\n"
        "- Expected artifacts: `formal/external_evidence/rl05_wave_equation_domain_01/rl05_reference_report.json`, "
        "`formal/external_evidence/rl05_wave_equation_domain_01/rl05_candidate_report.json`\n"
        "- Lock fingerprint must match the value below.\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
