from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np


RL08_TOLERANCE_PROFILE_ENV = "TOE_RL08_TOLERANCE_PROFILE"

RL08_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_invariant": 1e-10,
        "eps_break": 1e-3,
        "grid_order_eps": 1e-12,
    },
    "portable": {
        "eps_invariant": 1e-8,
        "eps_break": 1e-3,
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
    return repo_root / "formal" / "external_evidence" / "rl08_gauge_redundancy_invariance_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class RL08GaugeCase:
    case_id: str
    kind: str
    residual_maxabs: float

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "residual_maxabs": float(self.residual_maxabs),
        }


@dataclass(frozen=True)
class RL08GaugeReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    boundary: str
    x: list[float]
    psi_real: list[float]
    psi_imag: list[float]
    phi: list[float]
    rho: list[float]
    rho_gauge: list[float]
    obs_bad: list[float]
    obs_bad_gauge: list[float]
    cases: list[RL08GaugeCase]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "domain_tag": str(self.domain_tag),
            "params": dict(self.params),
            "boundary": str(self.boundary),
            "x": list(self.x),
            "psi_real": list(self.psi_real),
            "psi_imag": list(self.psi_imag),
            "phi": list(self.phi),
            "rho": list(self.rho),
            "rho_gauge": list(self.rho_gauge),
            "obs_bad": list(self.obs_bad),
            "obs_bad_gauge": list(self.obs_bad_gauge),
            "cases": [case.to_jsonable() for case in self.cases],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_rl08_report_artifact(path: Path) -> tuple[RL08GaugeReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "RL/gauge_redundancy_front_door_report/v1":
        raise ValueError(f"Unexpected RL08 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        RL08GaugeCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            residual_maxabs=float(case["residual_maxabs"]),
        )
        for case in payload["cases"]
    ]
    report = RL08GaugeReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "length": float(payload["params"]["length"]),
            "nx": float(payload["params"]["nx"]),
            "dx": float(payload["params"]["dx"]),
            "alpha": float(payload["params"]["alpha"]),
            "eps_invariant": float(payload["params"]["eps_invariant"]),
            "eps_break": float(payload["params"]["eps_break"]),
        },
        boundary=str(payload["boundary"]),
        x=[float(v) for v in payload["x"]],
        psi_real=[float(v) for v in payload["psi_real"]],
        psi_imag=[float(v) for v in payload["psi_imag"]],
        phi=[float(v) for v in payload["phi"]],
        rho=[float(v) for v in payload["rho"]],
        rho_gauge=[float(v) for v in payload["rho_gauge"]],
        obs_bad=[float(v) for v in payload["obs_bad"]],
        obs_bad_gauge=[float(v) for v in payload["obs_bad_gauge"]],
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def rl08_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(RL08_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in RL08_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL08_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {RL08_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def rl08_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in RL08_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL08_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(RL08_TOLERANCE_PROFILES[p])


def _is_nondecreasing(values: np.ndarray, *, eps: float) -> bool:
    if values.size <= 1:
        return True
    return bool(np.all(np.diff(values) >= -float(eps)))


def rl08_compare_surfaces(
    reference: RL08GaugeReport,
    candidate: RL08GaugeReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, RL08GaugeReport):
        raise TypeError("reference must be a RL08GaugeReport")
    if not isinstance(candidate, RL08GaugeReport):
        raise TypeError("candidate must be a RL08GaugeReport")

    ref_x = np.asarray(reference.x, dtype=float)
    cand_x = np.asarray(candidate.x, dtype=float)
    order_ref = _is_nondecreasing(ref_x, eps=float(tolerances["grid_order_eps"]))
    order_cand = _is_nondecreasing(cand_x, eps=float(tolerances["grid_order_eps"]))
    aligned = bool(ref_x.shape == cand_x.shape and np.array_equal(ref_x, cand_x))

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
        if not order_ref or not order_cand:
            reasons.append("FAIL_X_GRID_ORDER")
        if not aligned:
            reasons.append("FAIL_X_GRID_ALIGNMENT")
        if not bool(deterministic_ok):
            reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

        eps_invariant = float(tolerances["eps_invariant"])
        eps_break = float(tolerances["eps_break"])
        if cand_case.kind == "positive_control":
            if cand_case.residual_maxabs > eps_invariant:
                reasons.append("FAIL_GAUGE_INVARIANCE")
            if not reasons:
                reasons = ["rl08_gauge_invariance_ok"]
                passed = True
            else:
                passed = False
        else:
            if cand_case.residual_maxabs < eps_break:
                reasons.append("FAIL_GAUGE_BREAK_NOT_DETECTED")
            if not reasons:
                reasons = ["rl08_gauge_break_detected"]
                passed = True
            else:
                passed = False

        rows.append(
            {
                "artifact_id": f"RL08_GAUGE_{cand_case.case_id}",
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
                    "residual_maxabs": float(cand_case.residual_maxabs),
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
                    "x_grid_order_reference": bool(order_ref),
                    "x_grid_order_candidate": bool(order_cand),
                    "x_grid_aligned": bool(aligned),
                },
            }
        )

    return rows


@dataclass(frozen=True)
class RL08GaugeInvarianceV0Record:
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


def rl08_gauge_redundancy_invariance_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> RL08GaugeInvarianceV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else rl08_v0_tolerance_profile_from_env(env)
    tolerances = rl08_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "rl08_reference_report.json"
    cand_path = data_dir / "rl08_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return RL08GaugeInvarianceV0Record(
            schema="OV-RL-08_gauge_redundancy_invariance_comparator/v0",
            date=str(date),
            observable_id="OV-RL-08",
            domain_id="DRBR-DOMAIN-RL-08",
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

    reference, ref_deterministic = _load_rl08_report_artifact(ref_path)
    candidate, cand_deterministic = _load_rl08_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = rl08_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return RL08GaugeInvarianceV0Record(
        schema="OV-RL-08_gauge_redundancy_invariance_comparator/v0",
        date=str(date),
        observable_id="OV-RL-08",
        domain_id="DRBR-DOMAIN-RL-08",
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


def render_rl08_lock_markdown(record: RL08GaugeInvarianceV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-RL-08 - Gauge Redundancy Invariance Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted RL08 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.rl08_gauge_redundancy_invariance_front_door`\n"
        "- Outputs: `formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01/rl08_reference_report.json`, "
        "`formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01/rl08_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_rl08_gauge_redundancy_invariance_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
