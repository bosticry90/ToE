from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping


CT05_TOLERANCE_PROFILE_ENV = "TOE_CT05_TOLERANCE_PROFILE"

CT05_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_rep_invariant": 1e-10,
        "eps_bound_residual": 1e-3,
    },
    "portable": {
        "eps_rep_invariant": 1e-8,
        "eps_bound_residual": 5e-3,
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
    return repo_root / "formal" / "external_evidence" / "ct05_rep_invariant_admissibility_class_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class CT05RepInvariantCase:
    case_id: str
    kind: str
    admissible_ref: bool
    admissible_rep: bool
    bound_ok_ref: bool
    bound_ok_rep: bool
    bound_residual: float
    rep_delta: float

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "admissible_ref": bool(self.admissible_ref),
            "admissible_rep": bool(self.admissible_rep),
            "bound_ok_ref": bool(self.bound_ok_ref),
            "bound_ok_rep": bool(self.bound_ok_rep),
            "bound_residual": float(self.bound_residual),
            "rep_delta": float(self.rep_delta),
        }


@dataclass(frozen=True)
class CT05RepInvariantReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float | str]
    boundary: str
    cases: list[CT05RepInvariantCase]

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


def _load_ct05_report_artifact(path: Path) -> tuple[CT05RepInvariantReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "CT-05/rep_invariant_admissibility_class_front_door_report/v1":
        raise ValueError(f"Unexpected CT-05 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        CT05RepInvariantCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            admissible_ref=bool(case["admissible_ref"]),
            admissible_rep=bool(case["admissible_rep"]),
            bound_ok_ref=bool(case["bound_ok_ref"]),
            bound_ok_rep=bool(case["bound_ok_rep"]),
            bound_residual=float(case["bound_residual"]),
            rep_delta=float(case["rep_delta"]),
        )
        for case in payload["cases"]
    ]
    report = CT05RepInvariantReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "eps_rep_invariant": float(payload["params"]["eps_rep_invariant"]),
            "eps_bound_residual": float(payload["params"]["eps_bound_residual"]),
            "rep_break_delta": float(payload["params"]["rep_break_delta"]),
            "ct02_report_fingerprint": str(payload["params"]["ct02_report_fingerprint"]),
            "ct03_report_fingerprint": str(payload["params"]["ct03_report_fingerprint"]),
            "rl11_report_fingerprint": str(payload["params"]["rl11_report_fingerprint"]),
            "ct02_domain_tag": str(payload["params"]["ct02_domain_tag"]),
            "ct03_domain_tag": str(payload["params"]["ct03_domain_tag"]),
            "rl11_domain_tag": str(payload["params"]["rl11_domain_tag"]),
        },
        boundary=str(payload["boundary"]),
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def ct05_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CT05_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CT05_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT05_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CT05_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def ct05_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CT05_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT05_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CT05_TOLERANCE_PROFILES[p])


def _bool_residual(a: bool, b: bool) -> float:
    return float(abs(int(bool(a)) - int(bool(b))))


def ct05_compare_surfaces(
    reference: CT05RepInvariantReport,
    candidate: CT05RepInvariantReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, CT05RepInvariantReport):
        raise TypeError("reference must be a CT05RepInvariantReport")
    if not isinstance(candidate, CT05RepInvariantReport):
        raise TypeError("candidate must be a CT05RepInvariantReport")

    eps_rep_invariant = float(tolerances["eps_rep_invariant"])
    eps_bound_residual = float(tolerances["eps_bound_residual"])

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

        admissible_mismatch = _bool_residual(cand_case.admissible_ref, cand_case.admissible_rep) > eps_rep_invariant
        bound_mismatch = _bool_residual(cand_case.bound_ok_ref, cand_case.bound_ok_rep) > eps_rep_invariant
        if admissible_mismatch:
            reasons.append("FAIL_ADMISSIBILITY_MISMATCH")
        if bound_mismatch:
            reasons.append("FAIL_BOUND_STATUS_MISMATCH")

        if cand_case.kind == "positive_control":
            if not (cand_case.admissible_ref and cand_case.admissible_rep):
                reasons.append("FAIL_ADMISSIBILITY_NOT_DETECTED")
            if not (cand_case.bound_ok_ref and cand_case.bound_ok_rep):
                reasons.append("FAIL_BOUND_STATUS_MISMATCH")
            if cand_case.bound_residual > eps_bound_residual:
                reasons.append("FAIL_BOUND_RESIDUAL")
            if not reasons:
                reasons = ["ct05_rep_invariant_ok"]
                passed = True
            else:
                passed = False
        elif cand_case.kind == "negative_control_rep_break":
            if not (cand_case.admissible_ref and cand_case.admissible_rep):
                reasons.append("FAIL_ADMISSIBILITY_NOT_DETECTED")
            if not (cand_case.bound_ok_ref and cand_case.bound_ok_rep):
                reasons.append("FAIL_BOUND_STATUS_MISMATCH")
            if cand_case.bound_residual <= eps_bound_residual:
                reasons.append("FAIL_REP_BREAK_NOT_DETECTED")
            if not reasons:
                reasons = ["ct05_rep_break_detected"]
                passed = True
            else:
                passed = False
        elif cand_case.kind == "negative_control_admissibility":
            if cand_case.admissible_ref or cand_case.admissible_rep:
                reasons.append("FAIL_ADMISSIBILITY_NOT_DETECTED")
            if not reasons:
                reasons = ["ct05_admissibility_break_detected"]
                passed = True
            else:
                passed = False
        else:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
            passed = False

        rows.append(
            {
                "artifact_id": f"CT05_REP_INV_{cand_case.case_id}",
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
                    "admissible_ref": bool(cand_case.admissible_ref),
                    "admissible_rep": bool(cand_case.admissible_rep),
                    "bound_ok_ref": bool(cand_case.bound_ok_ref),
                    "bound_ok_rep": bool(cand_case.bound_ok_rep),
                    "bound_residual": float(cand_case.bound_residual),
                    "rep_delta": float(cand_case.rep_delta),
                    "eps_rep_invariant": float(eps_rep_invariant),
                    "eps_bound_residual": float(eps_bound_residual),
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
class CT05RepInvariantV0Record:
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


def ct05_rep_invariant_admissibility_class_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CT05RepInvariantV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else ct05_v0_tolerance_profile_from_env(env)
    tolerances = ct05_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "ct05_reference_report.json"
    cand_path = data_dir / "ct05_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return CT05RepInvariantV0Record(
            schema="CT-05_rep_invariant_admissibility_class_comparator/v0",
            date=str(date),
            observable_id="CT-05",
            domain_id="CT-DOMAIN-05",
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

    reference, ref_deterministic = _load_ct05_report_artifact(ref_path)
    candidate, cand_deterministic = _load_ct05_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = ct05_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return CT05RepInvariantV0Record(
        schema="CT-05_rep_invariant_admissibility_class_comparator/v0",
        date=str(date),
        observable_id="CT-05",
        domain_id="CT-DOMAIN-05",
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


def render_ct05_lock_markdown(record: CT05RepInvariantV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# CT-05 - Rep-Invariant Admissibility Class Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CT-05 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.ct05_rep_invariant_admissibility_class_front_door`\n"
        "- Outputs: `formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_reference_report.json`, "
        "`formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_ct05_rep_invariant_admissibility_class_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
