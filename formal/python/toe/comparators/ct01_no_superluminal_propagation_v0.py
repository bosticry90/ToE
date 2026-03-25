from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

from formal.python.meta.repo_environment import find_repo_root


CT01_TOLERANCE_PROFILE_ENV = "TOE_CT01_TOLERANCE_PROFILE"

CT01_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_ct01": 1e-8,
        "eps_break": 1e-3,
        "u_threshold": 1e-3,
    },
    "portable": {
        "eps_ct01": 1e-6,
        "eps_break": 1e-3,
        "u_threshold": 1e-3,
    },
}


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _relpath_from_repo(path: Path, repo_root: Path) -> str:
    p = path.resolve()
    root = repo_root.resolve()
    try:
        return str(p.relative_to(root)).replace("\\", "/")
    except ValueError:
        return str(p).replace("\\", "/")


@dataclass(frozen=True)
class CT01PropagationCase:
    case_id: str
    kind: str
    delta_x: float
    t_cross: float
    v_emp: float
    c_cone: float
    crossed: bool
    update_mode: str

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "delta_x": float(self.delta_x),
            "t_cross": float(self.t_cross),
            "v_emp": float(self.v_emp),
            "c_cone": float(self.c_cone),
            "crossed": bool(self.crossed),
            "update_mode": str(self.update_mode),
        }


@dataclass(frozen=True)
class CT01PropagationReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    boundary: str
    cases: list[CT01PropagationCase]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "domain_tag": str(self.domain_tag),
            "params": {k: float(v) for k, v in self.params.items()},
            "boundary": str(self.boundary),
            "cases": [c.to_jsonable() for c in self.cases],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d

    @staticmethod
    def from_jsonable(payload: Mapping[str, Any]) -> CT01PropagationReport:
        cases_raw = list(payload.get("cases") or [])
        cases = [
            CT01PropagationCase(
                case_id=str(c["case_id"]),
                kind=str(c["kind"]),
                delta_x=float(c["delta_x"]),
                t_cross=float(c["t_cross"]),
                v_emp=float(c["v_emp"]),
                c_cone=float(c["c_cone"]),
                crossed=bool(c["crossed"]),
                update_mode=str(c["update_mode"]),
            )
            for c in cases_raw
        ]
        return CT01PropagationReport(
            schema=str(payload["schema"]),
            config_tag=str(payload["config_tag"]),
            regime_tag=str(payload["regime_tag"]),
            domain_tag=str(payload["domain_tag"]),
            params={k: float(v) for k, v in dict(payload["params"]).items()},
            boundary=str(payload["boundary"]),
            cases=cases,
        )


@dataclass(frozen=True)
class CT01NoSuperluminalComparatorRecord:
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
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ct01_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    source = env if env is not None else os.environ
    raw = str(source.get(CT01_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    return raw if raw in CT01_TOLERANCE_PROFILES else "pinned"


def ct01_v0_tolerances(profile: str) -> dict[str, float]:
    key = str(profile).strip().lower()
    if key not in CT01_TOLERANCE_PROFILES:
        raise ValueError(f"Unsupported CT01 tolerance profile: {profile}")
    return dict(CT01_TOLERANCE_PROFILES[key])


def _load_ct01_report_artifact(path: Path) -> tuple[CT01PropagationReport | None, bool]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None, False

    try:
        report = CT01PropagationReport.from_jsonable(payload)
    except (KeyError, TypeError, ValueError):
        return None, False

    fp = str(payload.get("fingerprint", ""))
    return report, (fp == report.fingerprint())


def ct01_compare_surfaces(
    reference: CT01PropagationReport,
    candidate: CT01PropagationReport,
    *,
    tolerances: Mapping[str, float],
) -> list[dict[str, Any]]:
    if not isinstance(reference, CT01PropagationReport) or not isinstance(candidate, CT01PropagationReport):
        raise TypeError("ct01_compare_surfaces expects typed CT01PropagationReport inputs")

    eps_ct01 = float(tolerances["eps_ct01"])
    eps_break = float(tolerances["eps_break"])
    u_threshold = float(tolerances["u_threshold"])

    ref_by_case = {c.case_id: c for c in reference.cases}
    rows: list[dict[str, Any]] = []

    for cand_case in candidate.cases:
        ref_case = ref_by_case.get(cand_case.case_id)
        reasons: list[str] = []
        passed = True

        if ref_case is None:
            passed = False
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")
            c_cone = float(cand_case.c_cone)
            delta_x = float(cand_case.delta_x)
        else:
            c_cone = float(ref_case.c_cone)
            delta_x = float(ref_case.delta_x)
            if abs(float(cand_case.c_cone) - c_cone) > 1e-15 or abs(float(cand_case.delta_x) - delta_x) > 1e-15:
                passed = False
                reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")

        v_emp = float(cand_case.v_emp)
        crossed = bool(cand_case.crossed)

        if cand_case.kind == "positive_control":
            if not crossed:
                passed = False
                reasons.append("FAIL_NO_CROSSING")
            elif v_emp > c_cone + eps_ct01:
                passed = False
                reasons.append("FAIL_SUPERLUMINAL")
            else:
                reasons.append("ct01_within_cone")
        elif cand_case.kind == "negative_control":
            if not crossed:
                passed = False
                reasons.append("FAIL_NO_CROSSING")
            elif v_emp <= c_cone + eps_break:
                passed = False
                reasons.append("FAIL_BREAK_NOT_DETECTED")
            else:
                reasons.append("ct01_superluminal_detected")
        else:
            passed = False
            reasons.append("FAIL_DOMAIN_PARAMETER_INCONSISTENT")

        row = {
            "artifact_id": f"CT01_PROPAGATION_{cand_case.case_id}",
            "source": {
                "case_id": str(cand_case.case_id),
                "case_kind": str(cand_case.kind),
                "reference_schema": str(reference.schema),
                "candidate_schema": str(candidate.schema),
                "reference_config_tag": str(reference.config_tag),
                "candidate_config_tag": str(candidate.config_tag),
                "reference_regime_tag": str(reference.regime_tag),
                "candidate_regime_tag": str(candidate.regime_tag),
            },
            "input_fingerprint": str(candidate.fingerprint()),
            "input_data_fingerprint": str(candidate.fingerprint()),
            "metric_vector": {
                "delta_x": float(delta_x),
                "t_cross": float(cand_case.t_cross),
                "v_emp": float(v_emp),
                "c_cone": float(c_cone),
                "crossed": bool(crossed),
                "eps_ct01": float(eps_ct01),
                "eps_break": float(eps_break),
                "u_threshold": float(u_threshold),
            },
            "passed": bool(passed),
            "reason_codes": list(dict.fromkeys(reasons)),
            "diagnostics": {
                "reference_fingerprint": str(reference.fingerprint()),
                "candidate_fingerprint": str(candidate.fingerprint()),
            },
        }
        rows.append(row)

    return rows


def ct01_no_superluminal_v0_record(
    *,
    date: str,
    tolerance_profile: str | None = None,
    env: Mapping[str, str] | None = None,
    artifact_dir: Path | None = None,
) -> CT01NoSuperluminalComparatorRecord:
    repo_root = find_repo_root(Path(__file__))
    profile = str(tolerance_profile or ct01_v0_tolerance_profile_from_env(env)).strip().lower()
    tolerances = ct01_v0_tolerances(profile)

    default_dir = repo_root / "formal" / "external_evidence" / "ct01_no_superluminal_propagation_domain_01"
    artifacts_dir = (artifact_dir or default_dir).resolve()

    ref_path = artifacts_dir / "ct01_reference_report.json"
    cand_path = artifacts_dir / "ct01_candidate_report.json"

    status: dict[str, Any] = {"blocked": False, "reasons": []}

    inputs = {
        "artifact_dir": _relpath_from_repo(artifacts_dir, repo_root),
        "reference_artifact": _relpath_from_repo(ref_path, repo_root),
        "candidate_artifact": _relpath_from_repo(cand_path, repo_root),
    }

    if not ref_path.exists() or not cand_path.exists():
        status = {"blocked": True, "reasons": ["missing_domain_artifacts"]}
        return CT01NoSuperluminalComparatorRecord(
            schema="CT-01_no_superluminal_propagation_comparator/v0",
            date=str(date),
            observable_id="CT-01",
            domain_id="CT-DOMAIN-01",
            comparator_role="discriminative_candidate",
            tolerance_profile=profile,
            status=status,
            inputs=inputs,
            rows=[],
            summary={"counts": {"pass": 0, "fail": 0}, "artifacts": {"pass": [], "fail": []}},
            scope_limits=[
                "front_door_only",
                "typed_artifacts_only",
                "deterministic_record_only",
                "discriminative_candidate",
                "within_rep_only",
                "no_external_truth_claim",
            ],
        )

    reference, ref_ok = _load_ct01_report_artifact(ref_path)
    candidate, cand_ok = _load_ct01_report_artifact(cand_path)
    if reference is None or candidate is None:
        status = {"blocked": True, "reasons": ["invalid_domain_artifacts"]}
        rows: list[dict[str, Any]] = []
    else:
        rows = ct01_compare_surfaces(reference, candidate, tolerances=tolerances)

    if not ref_ok or not cand_ok:
        for row in rows:
            if "FAIL_NONDETERMINISTIC_FINGERPRINT" not in row["reason_codes"]:
                row["reason_codes"].append("FAIL_NONDETERMINISTIC_FINGERPRINT")
            row["passed"] = False

    pass_ids = [r["artifact_id"] for r in rows if bool(r.get("passed"))]
    fail_ids = [r["artifact_id"] for r in rows if not bool(r.get("passed"))]

    return CT01NoSuperluminalComparatorRecord(
        schema="CT-01_no_superluminal_propagation_comparator/v0",
        date=str(date),
        observable_id="CT-01",
        domain_id="CT-DOMAIN-01",
        comparator_role="discriminative_candidate",
        tolerance_profile=profile,
        status=status,
        inputs=inputs,
        rows=rows,
        summary={
            "counts": {"pass": len(pass_ids), "fail": len(fail_ids)},
            "artifacts": {"pass": pass_ids, "fail": fail_ids},
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


def render_ct01_lock_markdown(record: CT01NoSuperluminalComparatorRecord) -> str:
    payload = record.to_jsonable()
    json_block = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True)
    fp = record.fingerprint()

    return (
        "# CT-01 - No Superluminal Propagation Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted CT-01 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.ct01_no_superluminal_propagation_front_door`\n"
        "- Outputs: `formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_reference_report.json`, "
        "`formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_ct01_no_superluminal_propagation_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
