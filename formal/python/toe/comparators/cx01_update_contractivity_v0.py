from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping


CX01_TOLERANCE_PROFILE_ENV = "TOE_CX01_TOLERANCE_PROFILE"

CX01_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_contractivity": 1e-8,
        "eps_break": 1e-3,
    },
    "portable": {
        "eps_contractivity": 1e-6,
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
    return repo_root / "formal" / "external_evidence" / "cx01_update_contractivity_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class CX01ContractivityCase:
    case_id: str
    kind: str
    update_mode: str
    contraction_factor_per_step: float
    steps: int
    distance_in: float
    distance_out: float
    empirical_lipschitz: float

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "update_mode": str(self.update_mode),
            "contraction_factor_per_step": float(self.contraction_factor_per_step),
            "steps": int(self.steps),
            "distance_in": float(self.distance_in),
            "distance_out": float(self.distance_out),
            "empirical_lipschitz": float(self.empirical_lipschitz),
        }


@dataclass(frozen=True)
class CX01ContractivityReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    norm_name: str
    cases: list[CX01ContractivityCase]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "domain_tag": str(self.domain_tag),
            "params": dict(self.params),
            "norm_name": str(self.norm_name),
            "cases": [case.to_jsonable() for case in self.cases],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_cx01_report_artifact(path: Path) -> tuple[CX01ContractivityReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "CX-01/update_contractivity_front_door_report/v1":
        raise ValueError(f"Unexpected CX-01 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        CX01ContractivityCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            update_mode=str(case["update_mode"]),
            contraction_factor_per_step=float(case["contraction_factor_per_step"]),
            steps=int(case["steps"]),
            distance_in=float(case["distance_in"]),
            distance_out=float(case["distance_out"]),
            empirical_lipschitz=float(case["empirical_lipschitz"]),
        )
        for case in payload["cases"]
    ]
    report = CX01ContractivityReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "state_dim": float(payload["params"]["state_dim"]),
            "steps": float(payload["params"]["steps"]),
            "k_contract": float(payload["params"]["k_contract"]),
            "k_break": float(payload["params"]["k_break"]),
            "eps_contractivity": float(payload["params"]["eps_contractivity"]),
            "eps_break": float(payload["params"]["eps_break"]),
        },
        norm_name=str(payload["norm_name"]),
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def cx01_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CX01_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CX01_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CX01_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CX01_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def cx01_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CX01_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CX01_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CX01_TOLERANCE_PROFILES[p])


def cx01_compare_surfaces(
    reference: CX01ContractivityReport,
    candidate: CX01ContractivityReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, CX01ContractivityReport):
        raise TypeError("reference must be a CX01ContractivityReport")
    if not isinstance(candidate, CX01ContractivityReport):
        raise TypeError("candidate must be a CX01ContractivityReport")

    rows: list[dict[str, Any]] = []
    for ref_case, cand_case in zip(reference.cases, candidate.cases, strict=True):
        reasons: list[str] = []
        if reference.regime_tag != candidate.regime_tag:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if reference.domain_tag != candidate.domain_tag:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if reference.params != candidate.params:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if reference.norm_name != candidate.norm_name:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if ref_case.case_id != cand_case.case_id:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if not bool(deterministic_ok):
            reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

        eps_contractivity = float(tolerances["eps_contractivity"])
        eps_break = float(tolerances["eps_break"])
        admissibility_bound = 1.0

        # Comparator profile is semantically binding: artifact-declared eps values
        # must match the active comparator tolerances for a faithful replay record.
        ref_eps_contractivity = float(reference.params.get("eps_contractivity", float("nan")))
        ref_eps_break = float(reference.params.get("eps_break", float("nan")))
        cand_eps_contractivity = float(candidate.params.get("eps_contractivity", float("nan")))
        cand_eps_break = float(candidate.params.get("eps_break", float("nan")))
        if ref_eps_contractivity != eps_contractivity:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if ref_eps_break != eps_break:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if cand_eps_contractivity != eps_contractivity:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if cand_eps_break != eps_break:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")

        if cand_case.distance_in <= 0.0:
            reasons.append("FAIL_INVALID_DISTANCE")

        expected_empirical = abs(float(cand_case.contraction_factor_per_step)) ** int(cand_case.steps)
        if abs(float(cand_case.empirical_lipschitz) - float(expected_empirical)) > eps_contractivity:
            reasons.append("FAIL_EMPIRICAL_RATIO_INCONSISTENT")

        if cand_case.kind == "positive_control":
            if cand_case.empirical_lipschitz > admissibility_bound + eps_contractivity:
                reasons.append("FAIL_CONTRACTIVITY_VIOLATED")
            if not reasons:
                reasons = ["cx01_contractive_update_ok"]
                passed = True
            else:
                passed = False
        else:
            if cand_case.empirical_lipschitz <= admissibility_bound + eps_break:
                reasons.append("FAIL_BREAK_NOT_DETECTED")
            if not reasons:
                reasons = ["cx01_contractivity_break_detected"]
                passed = True
            else:
                passed = False

        rows.append(
            {
                "artifact_id": f"CX01_CONTRACTIVITY_{cand_case.case_id}",
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
                    "update_mode": str(cand_case.update_mode),
                    "contraction_factor_per_step": float(cand_case.contraction_factor_per_step),
                    "steps": int(cand_case.steps),
                    "distance_in": float(cand_case.distance_in),
                    "distance_out": float(cand_case.distance_out),
                    "empirical_lipschitz": float(cand_case.empirical_lipschitz),
                    "expected_empirical_lipschitz": float(expected_empirical),
                    "admissibility_bound": float(admissibility_bound),
                    "eps_contractivity": float(eps_contractivity),
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
class CX01UpdateContractivityV0Record:
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


def cx01_update_contractivity_v0_record(
    *,
    date: str = "2026-02-11",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CX01UpdateContractivityV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else cx01_v0_tolerance_profile_from_env(env)
    tolerances = cx01_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "cx01_reference_report.json"
    cand_path = data_dir / "cx01_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return CX01UpdateContractivityV0Record(
            schema="CX-01_update_contractivity_comparator/v0",
            date=str(date),
            observable_id="CX-01",
            domain_id="CX-DOMAIN-01",
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

    reference, ref_deterministic = _load_cx01_report_artifact(ref_path)
    candidate, cand_deterministic = _load_cx01_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = cx01_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return CX01UpdateContractivityV0Record(
        schema="CX-01_update_contractivity_comparator/v0",
        date=str(date),
        observable_id="CX-01",
        domain_id="CX-DOMAIN-01",
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
            "admissibility_predicate_only",
            "no_external_truth_claim",
        ],
    )


def render_cx01_lock_markdown(record: CX01UpdateContractivityV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# CX-01 - Update Contractivity Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CX-01 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- Admissibility predicate only (within-rep)\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.cx01_update_contractivity_front_door`\n"
        "- Outputs: `formal/external_evidence/cx01_update_contractivity_domain_01/cx01_reference_report.json`, "
        "`formal/external_evidence/cx01_update_contractivity_domain_01/cx01_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_cx01_update_contractivity_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
