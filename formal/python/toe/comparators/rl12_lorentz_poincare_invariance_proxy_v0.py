from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np


RL12_TOLERANCE_PROFILE_ENV = "TOE_RL12_TOLERANCE_PROFILE"

RL12_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_invariant": 1e-8,
        "eps_break": 1e-3,
    },
    "portable": {
        "eps_invariant": 1e-6,
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
    return repo_root / "formal" / "external_evidence" / "rl12_lorentz_poincare_invariance_proxy_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class RL12LorentzCase:
    case_id: str
    kind: str
    invariant_metric: float
    u: list[float]
    u_boosted: list[float]

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "invariant_metric": float(self.invariant_metric),
            "u": list(self.u),
            "u_boosted": list(self.u_boosted),
        }


@dataclass(frozen=True)
class RL12LorentzReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    boundary: str
    x: list[float]
    t: list[float]
    cases: list[RL12LorentzCase]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "domain_tag": str(self.domain_tag),
            "params": dict(self.params),
            "boundary": str(self.boundary),
            "x": list(self.x),
            "t": list(self.t),
            "cases": [case.to_jsonable() for case in self.cases],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_rl12_report_artifact(path: Path) -> tuple[RL12LorentzReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "RL/lorentz_poincare_invariance_front_door_report/v1":
        raise ValueError(f"Unexpected RL12 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        RL12LorentzCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            invariant_metric=float(case["invariant_metric"]),
            u=[float(v) for v in case["u"]],
            u_boosted=[float(v) for v in case["u_boosted"]],
        )
        for case in payload["cases"]
    ]
    report = RL12LorentzReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "length": float(payload["params"]["length"]),
            "time_window": float(payload["params"]["time_window"]),
            "nx": float(payload["params"]["nx"]),
            "nt": float(payload["params"]["nt"]),
            "dx": float(payload["params"]["dx"]),
            "dt": float(payload["params"]["dt"]),
            "c": float(payload["params"]["c"]),
            "beta": float(payload["params"]["beta"]),
            "gamma": float(payload["params"]["gamma"]),
            "eps_invariant": float(payload["params"]["eps_invariant"]),
            "eps_break": float(payload["params"]["eps_break"]),
        },
        boundary=str(payload["boundary"]),
        x=[float(v) for v in payload["x"]],
        t=[float(v) for v in payload["t"]],
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def rl12_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(RL12_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in RL12_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL12_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {RL12_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def rl12_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in RL12_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL12_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(RL12_TOLERANCE_PROFILES[p])


def rl12_compare_surfaces(
    reference: RL12LorentzReport,
    candidate: RL12LorentzReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, RL12LorentzReport):
        raise TypeError("reference must be a RL12LorentzReport")
    if not isinstance(candidate, RL12LorentzReport):
        raise TypeError("candidate must be a RL12LorentzReport")

    ref_x = np.asarray(reference.x, dtype=float)
    cand_x = np.asarray(candidate.x, dtype=float)
    ref_t = np.asarray(reference.t, dtype=float)
    cand_t = np.asarray(candidate.t, dtype=float)
    aligned = bool(
        ref_x.shape == cand_x.shape
        and ref_t.shape == cand_t.shape
        and np.array_equal(ref_x, cand_x)
        and np.array_equal(ref_t, cand_t)
    )

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
        if not aligned:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if not bool(deterministic_ok):
            reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

        eps_invariant = float(tolerances["eps_invariant"])
        eps_break = float(tolerances["eps_break"])
        if cand_case.kind == "positive_control":
            if cand_case.invariant_metric > eps_invariant:
                reasons.append("FAIL_LORENTZ_INVARIANCE")
            if not reasons:
                reasons = ["rl12_lorentz_invariance_ok"]
                passed = True
            else:
                passed = False
        else:
            if cand_case.invariant_metric < eps_break:
                reasons.append("FAIL_INVARIANCE_BREAK_NOT_DETECTED")
            if not reasons:
                reasons = ["rl12_invariance_break_detected"]
                passed = True
            else:
                passed = False

        rows.append(
            {
                "artifact_id": f"RL12_LORENTZ_{cand_case.case_id}",
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
                    "invariant_metric": float(cand_case.invariant_metric),
                    "eps_invariant": eps_invariant,
                    "eps_break": eps_break,
                },
                "passed": bool(passed),
                "reason_codes": list(reasons),
                "diagnostics": {
                    "reference_fingerprint": reference.fingerprint(),
                    "candidate_fingerprint": candidate.fingerprint(),
                    "x_count_reference": int(ref_x.size),
                    "x_count_candidate": int(cand_x.size),
                    "t_count_reference": int(ref_t.size),
                    "t_count_candidate": int(cand_t.size),
                    "grid_aligned": bool(aligned),
                },
            }
        )

    return rows


@dataclass(frozen=True)
class RL12LorentzInvarianceV0Record:
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


def rl12_lorentz_poincare_invariance_proxy_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> RL12LorentzInvarianceV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else rl12_v0_tolerance_profile_from_env(env)
    tolerances = rl12_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "rl12_reference_report.json"
    cand_path = data_dir / "rl12_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return RL12LorentzInvarianceV0Record(
            schema="OV-RL-12_lorentz_poincare_invariance_proxy_comparator/v0",
            date=str(date),
            observable_id="OV-RL-12",
            domain_id="DRBR-DOMAIN-RL-12",
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

    reference, ref_deterministic = _load_rl12_report_artifact(ref_path)
    candidate, cand_deterministic = _load_rl12_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = rl12_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return RL12LorentzInvarianceV0Record(
        schema="OV-RL-12_lorentz_poincare_invariance_proxy_comparator/v0",
        date=str(date),
        observable_id="OV-RL-12",
        domain_id="DRBR-DOMAIN-RL-12",
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


def render_rl12_lock_markdown(record: RL12LorentzInvarianceV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-RL-12 - Lorentz/Poincare Invariance Proxy Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted RL12 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.rl12_lorentz_poincare_invariance_proxy_front_door`\n"
        "- Outputs: `formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_reference_report.json`, "
        "`formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_rl12_lorentz_poincare_invariance_proxy_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
