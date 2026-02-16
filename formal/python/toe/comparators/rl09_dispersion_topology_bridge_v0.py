from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping

import numpy as np


RL09_TOLERANCE_PROFILE_ENV = "TOE_RL09_TOLERANCE_PROFILE"

RL09_TOLERANCE_PROFILES: dict[str, dict[str, float]] = {
    "pinned": {
        "eps_winding": 1e-8,
        "grid_order_eps": 1e-12,
    },
    "portable": {
        "eps_winding": 1e-6,
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
    return repo_root / "formal" / "external_evidence" / "rl09_dispersion_topology_bridge_domain_01"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class RL09TopologyCase:
    case_id: str
    kind: str
    t1: float
    t2: float
    dx: list[float]
    dy: list[float]
    energy: list[float]
    theta: list[float]
    theta_delta: float
    winding_raw: float
    winding_rounded: int
    abs_err: float
    min_energy: float

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "case_id": str(self.case_id),
            "kind": str(self.kind),
            "t1": float(self.t1),
            "t2": float(self.t2),
            "dx": list(self.dx),
            "dy": list(self.dy),
            "energy": list(self.energy),
            "theta": list(self.theta),
            "theta_delta": float(self.theta_delta),
            "winding_raw": float(self.winding_raw),
            "winding_rounded": int(self.winding_rounded),
            "abs_err": float(self.abs_err),
            "min_energy": float(self.min_energy),
        }


@dataclass(frozen=True)
class RL09TopologyReport:
    schema: str
    config_tag: str
    regime_tag: str
    domain_tag: str
    params: dict[str, float]
    boundary: str
    k: list[float]
    cases: list[RL09TopologyCase]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "config_tag": str(self.config_tag),
            "regime_tag": str(self.regime_tag),
            "domain_tag": str(self.domain_tag),
            "params": dict(self.params),
            "boundary": str(self.boundary),
            "k": list(self.k),
            "cases": [case.to_jsonable() for case in self.cases],
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def _load_rl09_report_artifact(path: Path) -> tuple[RL09TopologyReport, bool]:
    payload = _load_json(path)
    if str(payload.get("schema", "")) != "RL/dispersion_topology_front_door_report/v1":
        raise ValueError(f"Unexpected RL09 report schema in {path}: {payload.get('schema')!r}")

    cases = [
        RL09TopologyCase(
            case_id=str(case["case_id"]),
            kind=str(case["kind"]),
            t1=float(case["t1"]),
            t2=float(case["t2"]),
            dx=[float(v) for v in case["dx"]],
            dy=[float(v) for v in case["dy"]],
            energy=[float(v) for v in case["energy"]],
            theta=[float(v) for v in case["theta"]],
            theta_delta=float(case["theta_delta"]),
            winding_raw=float(case["winding_raw"]),
            winding_rounded=int(case["winding_rounded"]),
            abs_err=float(case["abs_err"]),
            min_energy=float(case["min_energy"]),
        )
        for case in payload["cases"]
    ]
    report = RL09TopologyReport(
        schema=str(payload["schema"]),
        config_tag=str(payload["config_tag"]),
        regime_tag=str(payload["regime_tag"]),
        domain_tag=str(payload["domain_tag"]),
        params={
            "length": float(payload["params"]["length"]),
            "nk": float(payload["params"]["nk"]),
            "t1_pos": float(payload["params"]["t1_pos"]),
            "t2_pos": float(payload["params"]["t2_pos"]),
            "t1_neg": float(payload["params"]["t1_neg"]),
            "t2_neg": float(payload["params"]["t2_neg"]),
            "eps_winding": float(payload["params"]["eps_winding"]),
        },
        boundary=str(payload["boundary"]),
        k=[float(v) for v in payload["k"]],
        cases=cases,
    )
    fp_declared = str(payload.get("fingerprint", ""))
    fp_recomputed = report.fingerprint()
    return report, fp_declared == fp_recomputed


def rl09_v0_tolerance_profile_from_env(env: Mapping[str, str] | None = None) -> str:
    src = env if env is not None else os.environ
    profile = str(src.get(RL09_TOLERANCE_PROFILE_ENV, "pinned")).strip().lower()
    if profile not in RL09_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL09_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported {RL09_TOLERANCE_PROFILE_ENV} profile '{profile}'. Allowed: {allowed}")
    return profile


def rl09_v0_tolerances(profile: str) -> dict[str, float]:
    p = str(profile).strip().lower()
    if p not in RL09_TOLERANCE_PROFILES:
        allowed = ", ".join(sorted(RL09_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unsupported tolerance profile '{profile}'. Allowed: {allowed}")
    return dict(RL09_TOLERANCE_PROFILES[p])


def _is_nondecreasing(values: np.ndarray, *, eps: float) -> bool:
    if values.size <= 1:
        return True
    return bool(np.all(np.diff(values) >= -float(eps)))


def rl09_compare_surfaces(
    reference: RL09TopologyReport,
    candidate: RL09TopologyReport,
    *,
    tolerances: Mapping[str, float],
    deterministic_ok: bool = True,
) -> list[dict[str, Any]]:
    if not isinstance(reference, RL09TopologyReport):
        raise TypeError("reference must be a RL09TopologyReport")
    if not isinstance(candidate, RL09TopologyReport):
        raise TypeError("candidate must be a RL09TopologyReport")

    ref_k = np.asarray(reference.k, dtype=float)
    cand_k = np.asarray(candidate.k, dtype=float)
    order_ref = _is_nondecreasing(ref_k, eps=float(tolerances["grid_order_eps"]))
    order_cand = _is_nondecreasing(cand_k, eps=float(tolerances["grid_order_eps"]))
    aligned = bool(ref_k.shape == cand_k.shape and np.array_equal(ref_k, cand_k))

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
            reasons.append("FAIL_K_GRID_ORDER")
        if not aligned:
            reasons.append("FAIL_K_GRID_ALIGNMENT")
        if not bool(deterministic_ok):
            reasons.append("FAIL_NONDETERMINISTIC_FINGERPRINT")

        eps_winding = float(tolerances["eps_winding"])
        target = 1.0 if cand_case.kind == "positive_control" else 0.0
        if abs(cand_case.winding_raw - target) > eps_winding:
            reasons.append("FAIL_WINDING_TARGET_MISMATCH")

        if not reasons:
            reasons = ["rl09_winding_target_satisfied"]
            passed = True
        else:
            passed = False

        rows.append(
            {
                "artifact_id": f"RL09_TOPOLOGY_{cand_case.case_id}",
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
                    "winding_raw": float(cand_case.winding_raw),
                    "winding_rounded": int(cand_case.winding_rounded),
                    "abs_err": float(cand_case.abs_err),
                    "min_energy": float(cand_case.min_energy),
                    "target_winding": target,
                },
                "passed": bool(passed),
                "reason_codes": list(reasons),
                "diagnostics": {
                    "reference_fingerprint": reference.fingerprint(),
                    "candidate_fingerprint": candidate.fingerprint(),
                    "k_count_reference": int(ref_k.size),
                    "k_count_candidate": int(cand_k.size),
                    "k_grid_order_reference": bool(order_ref),
                    "k_grid_order_candidate": bool(order_cand),
                    "k_grid_aligned": bool(aligned),
                },
            }
        )

    return rows


@dataclass(frozen=True)
class RL09DispersionTopologyV0Record:
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


def rl09_dispersion_topology_bridge_v0_record(
    *,
    date: str = "2026-02-09",
    tolerance_profile: str | None = None,
    artifact_dir: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> RL09DispersionTopologyV0Record:
    profile = str(tolerance_profile).strip().lower() if tolerance_profile is not None else rl09_v0_tolerance_profile_from_env(env)
    tolerances = rl09_v0_tolerances(profile)

    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()
    ref_path = data_dir / "rl09_reference_report.json"
    cand_path = data_dir / "rl09_candidate_report.json"
    missing = [str(p) for p in [ref_path, cand_path] if not p.exists()]
    if missing:
        return RL09DispersionTopologyV0Record(
            schema="OV-RL-09_dispersion_topology_bridge_comparator/v0",
            date=str(date),
            observable_id="OV-RL-09",
            domain_id="DRBR-DOMAIN-RL-09",
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

    reference, ref_deterministic = _load_rl09_report_artifact(ref_path)
    candidate, cand_deterministic = _load_rl09_report_artifact(cand_path)
    deterministic_ok = bool(ref_deterministic and cand_deterministic)

    rows = rl09_compare_surfaces(
        reference,
        candidate,
        tolerances=tolerances,
        deterministic_ok=deterministic_ok,
    )

    passed = [r for r in rows if r["passed"]]
    failed = [r for r in rows if not r["passed"]]

    return RL09DispersionTopologyV0Record(
        schema="OV-RL-09_dispersion_topology_bridge_comparator/v0",
        date=str(date),
        observable_id="OV-RL-09",
        domain_id="DRBR-DOMAIN-RL-09",
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


def render_rl09_lock_markdown(record: RL09DispersionTopologyV0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-RL-09 - Dispersion-Topology Bridge Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed/fingerprinted RL09 report artifacts only\n"
        "- Expectation-aware pass semantics for positive/negative controls\n"
        "- No external truth claim\n\n"
        "Reproduce (pinned)\n"
        "- Command: `.\\py.ps1 -m formal.python.tools.rl09_dispersion_topology_bridge_front_door`\n"
        "- Outputs: `formal/external_evidence/rl09_dispersion_topology_bridge_domain_01/rl09_reference_report.json`, "
        "`formal/external_evidence/rl09_dispersion_topology_bridge_domain_01/rl09_candidate_report.json`\n"
        "- Verify: `.\\py.ps1 -m pytest formal/python/tests/test_rl09_dispersion_topology_bridge_v0_lock.py -q`\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
