from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping


RL13_TOLERANCE_PROFILE_ENV = "TOE_RL13_TOLERANCE_PROFILE"

RL13_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_addition": 1e-8,
        "eps_break": 1e-3,
    },
    "portable": {
        "eps_addition": 1e-6,
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
    return repo_root / "formal" / "external_evidence" / "rl13_velocity_addition_group_law_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class RL13VelocityCase:
    case_id: str
    kind: str
    beta_u: float
    beta_v: float
    beta_comp: float
    beta_expected: float
    addition_residual: float

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "beta_u": float(self.beta_u),
            "beta_v": float(self.beta_v),
            "beta_comp": float(self.beta_comp),
            "beta_expected": float(self.beta_expected),
            "addition_residual": float(self.addition_residual),
        }


@dataclass(frozen=True)
class RL13VelocityReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    boundary: str
    cases: list[RL13VelocityCase]

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


def _load_rl13_report_artifact(path: Path) -> tuple[RL13VelocityReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "RL/velocity_addition_front_door_report/v1":
        raise ValueError(f"Unexpected RL13 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        RL13VelocityCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            beta_u=float(case["beta_u"]),
            beta_v=float(case["beta_v"]),
            beta_comp=float(case["beta_comp"]),
            beta_expected=float(case["beta_expected"]),
            addition_residual=float(case["addition_residual"]),
        )
        for case in payload["cases"]
    ]
    report = RL13VelocityReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "c": float(payload["params"]["c"]),
            "beta_u": float(payload["params"]["beta_u"]),
            "beta_v": float(payload["params"]["beta_v"]),
            "eps_addition": float(payload["params"]["eps_addition"]),
            "eps_break": float(payload["params"]["eps_break"]),
        },
        boundary=str(payload["boundary"]),
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def rl13_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(RL13_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in RL13_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL13_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {RL13_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def rl13_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in RL13_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL13_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(RL13_TOLERANCE_PROFILES[p])


def _einstein_add(beta_u: float, beta_v: float) -> float:
    return (beta_u + beta_v) / (1.0 + beta_u * beta_v)


def rl13_compare_surfaces(
    reference: RL13VelocityReport,
    candidate: RL13VelocityReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, RL13VelocityReport):
        raise TypeError("reference must be a RL13VelocityReport")
    if not isinstance(candidate, RL13VelocityReport):
        raise TypeError("candidate must be a RL13VelocityReport")

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

        beta_expected = _einstein_add(cand_case.beta_u, cand_case.beta_v)
        addition_residual = abs(cand_case.beta_comp - beta_expected)
        if abs(addition_residual - float(cand_case.addition_residual)) > 1e-12:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")

        eps_addition = float(tolerances["eps_addition"])
        eps_break = float(tolerances["eps_break"])
        if cand_case.kind == "positive_control":
            if addition_residual > eps_addition:
                reasons.append("FAIL_ADDITION_LAW")
            if not reasons:
                reasons = ["rl13_velocity_addition_ok"]
                passed = True
            else:
                passed = False
        else:
            if addition_residual < eps_break:
                reasons.append("FAIL_BREAK_NOT_DETECTED")
            if not reasons:
                reasons = ["rl13_addition_break_detected"]
                passed = True
            else:
                passed = False

        rows.append(
            {
                "artifact_id": f"RL13_VELOCITY_{cand_case.case_id}",
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
                    "beta_u": float(cand_case.beta_u),
                    "beta_v": float(cand_case.beta_v),
                    "beta_comp": float(cand_case.beta_comp),
                    "beta_expected": float(beta_expected),
                    "addition_residual": float(addition_residual),
                    "eps_addition": eps_addition,
                    "eps_break": eps_break,
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
class RL13VelocityAdditionV0Record:
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


def rl13_velocity_addition_group_law_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> RL13VelocityAdditionV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else rl13_v0_tolerance_profile_from_env(env)
    tolerances = rl13_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "rl13_reference_report.json"
    cand_path = data_dir / "rl13_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return RL13VelocityAdditionV0Record(
            schema="OV-RL-13_velocity_addition_group_law_comparator/v0",
            date=str(date),
            observable_id="OV-RL-13",
            domain_id="DRBR-DOMAIN-RL-13",
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

    reference, ref_deterministic = _load_rl13_report_artifact(ref_path)
    candidate, cand_deterministic = _load_rl13_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = rl13_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return RL13VelocityAdditionV0Record(
        schema="OV-RL-13_velocity_addition_group_law_comparator/v0",
        date=str(date),
        observable_id="OV-RL-13",
        domain_id="DRBR-DOMAIN-RL-13",
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


def render_rl13_lock_markdown(record: RL13VelocityAdditionV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-RL-13 - Velocity Addition Group-Law Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted RL13 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.rl13_velocity_addition_group_law_front_door`\n"
        "- Outputs: `formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_reference_report.json`, "
        "`formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_rl13_velocity_addition_group_law_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
