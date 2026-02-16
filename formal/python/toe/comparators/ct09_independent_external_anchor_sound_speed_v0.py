from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping


CT09_TOLERANCE_PROFILE_ENV = "TOE_CT09_TOLERANCE_PROFILE"

CT09_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_rmse_um": 30.0,
        "eps_max_abs_error_um": 50.0,
        "eps_reduced_chi2": 2.8,
    },
    "portable": {
        "eps_rmse_um": 31.0,
        "eps_max_abs_error_um": 52.5,
        "eps_reduced_chi2": 2.9,
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
    return repo_root / "formal" / "external_evidence" / "ct09_independent_sound_speed_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class CT09IndependentAnchorCase:
    case_id: str
    kind: str
    model_tag: str
    c_um_per_ms: float
    intercept_um: float
    rmse_um: float
    max_abs_error_um: float
    reduced_chi2: float
    n_points: int

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "model_tag": str(self.model_tag),
            "c_um_per_ms": float(self.c_um_per_ms),
            "intercept_um": float(self.intercept_um),
            "rmse_um": float(self.rmse_um),
            "max_abs_error_um": float(self.max_abs_error_um),
            "reduced_chi2": float(self.reduced_chi2),
            "n_points": int(self.n_points),
        }


@dataclass(frozen=True)
class CT09IndependentAnchorReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float | str]
    boundary: str
    cases: list[CT09IndependentAnchorCase]

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


def _load_ct09_report_artifact(path: Path) -> tuple[CT09IndependentAnchorReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "CT-09/independent_external_anchor_sound_speed_front_door_report/v1":
        raise ValueError(f"Unexpected CT-09 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        CT09IndependentAnchorCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            model_tag=str(case["model_tag"]),
            c_um_per_ms=float(case["c_um_per_ms"]),
            intercept_um=float(case["intercept_um"]),
            rmse_um=float(case["rmse_um"]),
            max_abs_error_um=float(case["max_abs_error_um"]),
            reduced_chi2=float(case["reduced_chi2"]),
            n_points=int(case["n_points"]),
        )
        for case in payload["cases"]
    ]
    report = CT09IndependentAnchorReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "dataset_id": str(payload["params"]["dataset_id"]),
            "dataset_csv_relpath": str(payload["params"]["dataset_csv_relpath"]),
            "dataset_csv_sha256": str(payload["params"]["dataset_csv_sha256"]),
            "preprocessing_tag": str(payload["params"]["preprocessing_tag"]),
            "observable_id": str(payload["params"]["observable_id"]),
            "fit_model": str(payload["params"]["fit_model"]),
            "c_scale_negative": float(payload["params"]["c_scale_negative"]),
            "sigma_distance_um": float(payload["params"]["sigma_distance_um"]),
            "eps_rmse_um": float(payload["params"]["eps_rmse_um"]),
            "eps_max_abs_error_um": float(payload["params"]["eps_max_abs_error_um"]),
            "eps_reduced_chi2": float(payload["params"]["eps_reduced_chi2"]),
        },
        boundary=str(payload["boundary"]),
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def ct09_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CT09_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CT09_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT09_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CT09_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def ct09_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CT09_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT09_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CT09_TOLERANCE_PROFILES[p])


def ct09_compare_surfaces(
    reference: CT09IndependentAnchorReport,
    candidate: CT09IndependentAnchorReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, CT09IndependentAnchorReport):
        raise TypeError("reference must be a CT09IndependentAnchorReport")
    if not isinstance(candidate, CT09IndependentAnchorReport):
        raise TypeError("candidate must be a CT09IndependentAnchorReport")

    eps_rmse = float(tolerances["eps_rmse_um"])
    eps_max_abs = float(tolerances["eps_max_abs_error_um"])
    eps_chi2 = float(tolerances["eps_reduced_chi2"])

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

        # Comparator profile is semantically binding: artifact-declared eps values
        # must match the active comparator tolerances for a faithful replay record.
        ref_eps_rmse = float(reference.params.get("eps_rmse_um", float("nan")))
        ref_eps_max_abs = float(reference.params.get("eps_max_abs_error_um", float("nan")))
        ref_eps_chi2 = float(reference.params.get("eps_reduced_chi2", float("nan")))
        cand_eps_rmse = float(candidate.params.get("eps_rmse_um", float("nan")))
        cand_eps_max_abs = float(candidate.params.get("eps_max_abs_error_um", float("nan")))
        cand_eps_chi2 = float(candidate.params.get("eps_reduced_chi2", float("nan")))
        if ref_eps_rmse != eps_rmse:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if ref_eps_max_abs != eps_max_abs:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if ref_eps_chi2 != eps_chi2:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if cand_eps_rmse != eps_rmse:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if cand_eps_max_abs != eps_max_abs:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
        if cand_eps_chi2 != eps_chi2:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")

        within_tol = bool(
            cand_case.rmse_um <= eps_rmse
            and cand_case.max_abs_error_um <= eps_max_abs
            and cand_case.reduced_chi2 <= eps_chi2
        )

        if cand_case.kind == "positive_control":
            if not within_tol:
                reasons.append("FAIL_TOLERANCE_EXCEEDED")
            if not reasons:
                reasons = ["ct09_independent_anchor_fit_ok"]
                passed = True
            else:
                passed = False
        elif cand_case.kind == "negative_control_model_break":
            if within_tol:
                reasons.append("FAIL_NEGATIVE_CONTROL_NOT_DETECTED")
            if not reasons:
                reasons = ["ct09_independent_anchor_failure_detected"]
                passed = True
            else:
                passed = False
        else:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
            passed = False

        rows.append(
            {
                "artifact_id": f"CT09_INDEPENDENT_ANCHOR_{cand_case.case_id}",
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
                    "model_tag": str(cand_case.model_tag),
                    "c_um_per_ms": float(cand_case.c_um_per_ms),
                    "intercept_um": float(cand_case.intercept_um),
                    "rmse_um": float(cand_case.rmse_um),
                    "max_abs_error_um": float(cand_case.max_abs_error_um),
                    "reduced_chi2": float(cand_case.reduced_chi2),
                    "n_points": int(cand_case.n_points),
                    "eps_rmse_um": float(eps_rmse),
                    "eps_max_abs_error_um": float(eps_max_abs),
                    "eps_reduced_chi2": float(eps_chi2),
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
class CT09IndependentAnchorV0Record:
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


def ct09_independent_external_anchor_sound_speed_v0_record(
    *,
    date: str = "2026-02-11",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CT09IndependentAnchorV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else ct09_v0_tolerance_profile_from_env(env)
    tolerances = ct09_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "ct09_reference_report.json"
    cand_path = data_dir / "ct09_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return CT09IndependentAnchorV0Record(
            schema="CT-09_independent_external_anchor_sound_speed_comparator/v0",
            date=str(date),
            observable_id="CT-09",
            domain_id="CT-DOMAIN-09",
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

    reference, ref_deterministic = _load_ct09_report_artifact(ref_path)
    candidate, cand_deterministic = _load_ct09_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = ct09_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return CT09IndependentAnchorV0Record(
        schema="CT-09_independent_external_anchor_sound_speed_comparator/v0",
        date=str(date),
        observable_id="CT-09",
        domain_id="CT-DOMAIN-09",
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
            "external_anchor_only",
            "no_external_truth_claim",
        ],
    )


def render_ct09_lock_markdown(record: CT09IndependentAnchorV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# CT-09 - Independent External Anchor Sound-Speed Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CT-09 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- Independent external-anchor lane only\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.ct09_independent_external_anchor_sound_speed_front_door`\n"
        "- Outputs: `formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_reference_report.json`, "
        "`formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_ct09_independent_external_anchor_sound_speed_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
