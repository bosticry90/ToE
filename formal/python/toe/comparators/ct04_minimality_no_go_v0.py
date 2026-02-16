from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np


CT04_TOLERANCE_PROFILE_ENV = "TOE_CT04_TOLERANCE_PROFILE"

CT04_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_drift": 5e-3,
        "eps_break": 1e-3,
    },
    "portable": {
        "eps_drift": 1e-2,
        "eps_break": 1e-3,
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
    return repo_root / "formal" / "external_evidence" / "ct04_minimality_no_go_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class CT04MinimalityCase:
    case_id: str
    kind: str
    constraint_mode: str
    dt: float
    steps: int
    cfl: float
    rel_drift: float
    max_rel_drift: float

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "constraint_mode": str(self.constraint_mode),
            "dt": float(self.dt),
            "steps": int(self.steps),
            "cfl": float(self.cfl),
            "rel_drift": float(self.rel_drift),
            "max_rel_drift": float(self.max_rel_drift),
        }


@dataclass(frozen=True)
class CT04MinimalityReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    boundary: str
    cases: list[CT04MinimalityCase]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "domain_tag": str(self.domain_tag),
            "params": dict(self.params),
            "boundary": str(self.boundary),
            "cases": [case.to_jsonable() for case in self.cases],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_ct04_report_artifact(path: Path) -> tuple[CT04MinimalityReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "CT-04/minimality_no_go_front_door_report/v1":
        raise ValueError(f"Unexpected CT-04 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        CT04MinimalityCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            constraint_mode=str(case["constraint_mode"]),
            dt=float(case["dt"]),
            steps=int(case["steps"]),
            cfl=float(case["cfl"]),
            rel_drift=float(case["rel_drift"]),
            max_rel_drift=float(case["max_rel_drift"]),
        )
        for case in payload["cases"]
    ]
    report = CT04MinimalityReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "length": float(payload["params"]["length"]),
            "nx": float(payload["params"]["nx"]),
            "dx": float(payload["params"]["dx"]),
            "c_wave": float(payload["params"]["c_wave"]),
            "dt_pos": float(payload["params"]["dt_pos"]),
            "dt_neg": float(payload["params"]["dt_neg"]),
            "steps_pos": float(payload["params"]["steps_pos"]),
            "steps_neg": float(payload["params"]["steps_neg"]),
            "cfl_max": float(payload["params"]["cfl_max"]),
            "eps_drift": float(payload["params"]["eps_drift"]),
            "eps_break": float(payload["params"]["eps_break"]),
        },
        boundary=str(payload["boundary"]),
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def ct04_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CT04_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CT04_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT04_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CT04_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def ct04_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CT04_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT04_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CT04_TOLERANCE_PROFILES[p])


def ct04_compare_surfaces(
    reference: CT04MinimalityReport,
    candidate: CT04MinimalityReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, CT04MinimalityReport):
        raise TypeError("reference must be a CT04MinimalityReport")
    if not isinstance(candidate, CT04MinimalityReport):
        raise TypeError("candidate must be a CT04MinimalityReport")

    rows: list[dict[str, Any]] = []
    for ref_case, cand_case in zip(reference.cases, candidate.cases, strict=True):
        reasons: list[str] = []
        if reference.regime_tag != candidate.regime_tag:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if reference.domain_tag != candidate.domain_tag:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if reference.params != candidate.params:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if reference.boundary != candidate.boundary:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if ref_case.case_id != cand_case.case_id:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if not bool(deterministic_ok):
            reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

        eps_drift = float(tolerances["eps_drift"])
        eps_break = float(tolerances["eps_break"])
        cfl_max = float(reference.params["cfl_max"])

        if cand_case.kind == "positive_control":
            if cand_case.cfl > cfl_max + eps_break:
                reasons.append("FAIL_CFL_BOUND")
            if cand_case.rel_drift > eps_drift:
                reasons.append("FAIL_ENERGY_DRIFT_EXCEEDS")
            if cand_case.max_rel_drift > eps_drift:
                reasons.append("FAIL_ENERGY_DRIFT_EXCEEDS")
            if not reasons:
                reasons = ["ct04_minimality_ok"]
                passed = True
            else:
                passed = False
        else:
            if cand_case.cfl <= cfl_max + eps_break:
                reasons.append("FAIL_BREAK_NOT_DETECTED")
            if not reasons:
                reasons = ["ct04_minimality_violation_detected"]
                passed = True
            else:
                passed = False

        rows.append(
            {
                "artifact_id": f"CT04_MINIMALITY_{cand_case.case_id}",
                "source": {
                    "reference_schema": reference.schema,
                    "candidate_schema": candidate.schema,
                    "reference_config_tag": reference.config_tag,
                    "candidate_config_tag": candidate.config_tag,
                    "reference_regime_tag": reference.regime_tag,
                    "candidate_regime_tag": candidate.regime_tag,
                    "case_id": cand_case.case_id,
                    "case_kind": cand_case.kind,
                },
                "input_fingerprint": candidate.fingerprint(),
                "input_data_fingerprint": candidate.fingerprint(),
                "metric_vector": {
                    "constraint_mode": str(cand_case.constraint_mode),
                    "dt": float(cand_case.dt),
                    "steps": int(cand_case.steps),
                    "cfl": float(cand_case.cfl),
                    "rel_drift": float(cand_case.rel_drift),
                    "max_rel_drift": float(cand_case.max_rel_drift),
                    "cfl_max": float(cfl_max),
                    "eps_drift": float(eps_drift),
                    "eps_break": float(eps_break),
                },
                "passed": bool(passed),
                "reason_codes": list(reasons),
                "diagnostics": {
                    "reference_fingerprint": reference.fingerprint(),
                    "candidate_fingerprint": candidate.fingerprint(),
                },
            }
        )

    return rows


@dataclass(frozen=True)
class CT04MinimalityV0Record:
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


def ct04_minimality_no_go_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CT04MinimalityV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else ct04_v0_tolerance_profile_from_env(env)
    tolerances = ct04_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "ct04_reference_report.json"
    cand_path = data_dir / "ct04_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return CT04MinimalityV0Record(
            schema="CT-04_minimality_no_go_comparator/v0",
            date=str(date),
            observable_id="CT-04",
            domain_id="CT-DOMAIN-04",
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

    reference, ref_deterministic = _load_ct04_report_artifact(ref_path)
    candidate, cand_deterministic = _load_ct04_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = ct04_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return CT04MinimalityV0Record(
        schema="CT-04_minimality_no_go_comparator/v0",
        date=str(date),
        observable_id="CT-04",
        domain_id="CT-DOMAIN-04",
        comparator_role="discriminative_candidate",
        tolerance_profile=profile,
        status={"blocked": False, "reasons": []},
        inputs={
            "artifact_dir": _relpath(repo_root, data_dir),
            "reference_artifact": _relpath(repo_root, ref_path),
            "candidate_artifact": _relpath(repo_root, cand_path),
        },
        rows=rows,
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


def render_ct04_lock_markdown(record: CT04MinimalityV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# CT-04 - Minimality No-Go Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CT-04 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.ct04_minimality_no_go_front_door`\n"
        "- Outputs: `formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_reference_report.json`, "
        "`formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_ct04_minimality_no_go_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
