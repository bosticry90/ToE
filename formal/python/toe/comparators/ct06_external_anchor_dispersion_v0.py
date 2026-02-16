from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping


CT06_TOLERANCE_PROFILE_ENV = "TOE_CT06_TOLERANCE_PROFILE"

CT06_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_rmse_kHz": 0.25,
        "eps_max_abs_error_kHz": 0.50,
        "eps_reduced_chi2": 4.0,
    },
    "portable": {
        "eps_rmse_kHz": 0.35,
        "eps_max_abs_error_kHz": 0.70,
        "eps_reduced_chi2": 6.0,
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
    return repo_root / "formal" / "external_evidence" / "ct06_external_anchor_dispersion_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class CT06ExternalAnchorCase:
    case_id: str
    kind: str
    model_tag: str
    c_s2_kHz2_um2: float
    alpha_kHz2_um4: float
    rmse_kHz: float
    max_abs_error_kHz: float
    reduced_chi2: float
    n_points: int

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "model_tag": str(self.model_tag),
            "c_s2_kHz2_um2": float(self.c_s2_kHz2_um2),
            "alpha_kHz2_um4": float(self.alpha_kHz2_um4),
            "rmse_kHz": float(self.rmse_kHz),
            "max_abs_error_kHz": float(self.max_abs_error_kHz),
            "reduced_chi2": float(self.reduced_chi2),
            "n_points": int(self.n_points),
        }


@dataclass(frozen=True)
class CT06ExternalAnchorReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float | str]
    boundary: str
    cases: list[CT06ExternalAnchorCase]

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


def _load_ct06_report_artifact(path: Path) -> tuple[CT06ExternalAnchorReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "CT-06/external_anchor_dispersion_front_door_report/v1":
        raise ValueError(f"Unexpected CT-06 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        CT06ExternalAnchorCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            model_tag=str(case["model_tag"]),
            c_s2_kHz2_um2=float(case["c_s2_kHz2_um2"]),
            alpha_kHz2_um4=float(case["alpha_kHz2_um4"]),
            rmse_kHz=float(case["rmse_kHz"]),
            max_abs_error_kHz=float(case["max_abs_error_kHz"]),
            reduced_chi2=float(case["reduced_chi2"]),
            n_points=int(case["n_points"]),
        )
        for case in payload["cases"]
    ]
    report = CT06ExternalAnchorReport(
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
            "alpha_scale_negative": float(payload["params"]["alpha_scale_negative"]),
            "eps_rmse_kHz": float(payload["params"]["eps_rmse_kHz"]),
            "eps_max_abs_error_kHz": float(payload["params"]["eps_max_abs_error_kHz"]),
            "eps_reduced_chi2": float(payload["params"]["eps_reduced_chi2"]),
        },
        boundary=str(payload["boundary"]),
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def ct06_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(CT06_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in CT06_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT06_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {CT06_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def ct06_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in CT06_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(CT06_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(CT06_TOLERANCE_PROFILES[p])


def ct06_compare_surfaces(
    reference: CT06ExternalAnchorReport,
    candidate: CT06ExternalAnchorReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, CT06ExternalAnchorReport):
        raise TypeError("reference must be a CT06ExternalAnchorReport")
    if not isinstance(candidate, CT06ExternalAnchorReport):
        raise TypeError("candidate must be a CT06ExternalAnchorReport")

    eps_rmse = float(tolerances["eps_rmse_kHz"])
    eps_max_abs = float(tolerances["eps_max_abs_error_kHz"])
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

        within_tol = bool(
            cand_case.rmse_kHz <= eps_rmse
            and cand_case.max_abs_error_kHz <= eps_max_abs
            and cand_case.reduced_chi2 <= eps_chi2
        )

        if cand_case.kind == "positive_control":
            if not within_tol:
                reasons.append("FAIL_TOLERANCE_EXCEEDED")
            if not reasons:
                reasons = ["ct06_external_anchor_fit_ok"]
                passed = True
            else:
                passed = False
        elif cand_case.kind == "negative_control_model_break":
            if within_tol:
                reasons.append("FAIL_NEGATIVE_CONTROL_NOT_DETECTED")
            if not reasons:
                reasons = ["ct06_external_anchor_failure_detected"]
                passed = True
            else:
                passed = False
        else:
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
            passed = False

        rows.append(
            {
                "artifact_id": f"CT06_EXTERNAL_ANCHOR_{cand_case.case_id}",
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
                    "c_s2_kHz2_um2": float(cand_case.c_s2_kHz2_um2),
                    "alpha_kHz2_um4": float(cand_case.alpha_kHz2_um4),
                    "rmse_kHz": float(cand_case.rmse_kHz),
                    "max_abs_error_kHz": float(cand_case.max_abs_error_kHz),
                    "reduced_chi2": float(cand_case.reduced_chi2),
                    "n_points": int(cand_case.n_points),
                    "eps_rmse_kHz": float(eps_rmse),
                    "eps_max_abs_error_kHz": float(eps_max_abs),
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
class CT06ExternalAnchorV0Record:
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


def ct06_external_anchor_dispersion_v0_record(
    *,
    date: str = "2026-02-10",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> CT06ExternalAnchorV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else ct06_v0_tolerance_profile_from_env(env)
    tolerances = ct06_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "ct06_reference_report.json"
    cand_path = data_dir / "ct06_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return CT06ExternalAnchorV0Record(
            schema="CT-06_external_anchor_dispersion_comparator/v0",
            date=str(date),
            observable_id="CT-06",
            domain_id="CT-DOMAIN-06",
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

    reference, ref_deterministic = _load_ct06_report_artifact(ref_path)
    candidate, cand_deterministic = _load_ct06_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = ct06_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return CT06ExternalAnchorV0Record(
        schema="CT-06_external_anchor_dispersion_comparator/v0",
        date=str(date),
        observable_id="CT-06",
        domain_id="CT-DOMAIN-06",
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
            "external_anchor",
            "no_external_truth_claim",
        ],
    )


def render_ct06_lock_markdown(record: CT06ExternalAnchorV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# CT-06 - External Anchor Dispersion Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CT-06 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.ct06_external_anchor_dispersion_front_door`\n"
        "- Outputs: `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_reference_report.json`, "
        "`formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_ct06_external_anchor_dispersion_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )

