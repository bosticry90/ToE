"""OV-FN-WT-01: Pruning table for FN-01 weight-policy candidates (score-threshold).

Purpose
- Consume the locked FN-01 cross-fit metric residual report and the upstream FN
  candidate selection surface (OV-BR-FN-01), then prune *weight policies* that
  fail a declared maximum score threshold.

Scope / limits
- Summary-only / eliminative-only bookkeeping.
- Unknown is not fail.
- Numeric use is limited to applying declared thresholds to a locked scalar.
- Blocked-by-default if required input locks are missing, and may be BLOCKED by
  admissibility manifest (CT01/SYM01/CAUS01).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Literal

from formal.python.toe.constraints.admissibility_manifest import check_required_gates


SurvivalStatus = Literal["true", "false", "unknown"]


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing record fingerprint line")
    return m.group(1)


def _extract_fn01_r_metric(md_text: str) -> float | None:
    m = re.search(r"^\s*-\s*R_metric\s*=\s*([0-9eE+\-\.]+)\s*$", md_text, flags=re.MULTILINE)
    if m is None:
        return None
    try:
        return float(m.group(1))
    except ValueError:
        return None


@dataclass(frozen=True)
class OVFNWT01WeightPolicyPruningTableRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    rows: list[dict[str, Any]]

    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "rows": list(self.rows),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovfnwt01_weight_policy_pruning_table_record(
    *,
    date: str = "2026-01-25",
    residual_lock_path: Path | None = None,
    br_pruning_lock_path: Path | None = None,
    br_fn_pruning_lock_path: Path | None = None,
    policy_decl_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVFNWT01WeightPolicyPruningTableRecord:
    repo_root = _find_repo_root(Path(__file__))

    use_override_inputs = admissibility_manifest_path is not None

    default_residual = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "functionals"
        / "FN-01_cross_fit_metric_residual_DR02_DR03.md"
    )
    residual_path = (residual_lock_path or default_residual).resolve()

    default_dr_br = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / ("OV-DR-BR-01_candidate_pruning_table_OVERRIDE.md" if use_override_inputs else "OV-DR-BR-01_candidate_pruning_table.md")
    )
    dr_br_path = (br_pruning_lock_path or default_dr_br).resolve()

    default_br_fn = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / ("OV-BR-FN-01_fn01_metric_residual_pruning_table_OVERRIDE.md" if use_override_inputs else "OV-BR-FN-01_fn01_metric_residual_pruning_table.md")
    )
    br_fn_path = (br_fn_pruning_lock_path or default_br_fn).resolve()

    default_decl = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / ("OV-FN-WT-00_fn01_weight_policy_declarations_OVERRIDE.md" if use_override_inputs else "OV-FN-WT-00_fn01_weight_policy_declarations.md")
    )
    decl_path = (policy_decl_lock_path or default_decl).resolve()

    if not residual_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_input_lock_FN-01_cross_fit_metric_residual_DR02_DR03"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFNWT01WeightPolicyPruningTableRecord(
            schema="OV-FN-WT-01_fn01_weight_policy_pruning_table/v1",
            date=str(date),
            observable_id="OV-FN-WT-01",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": False,
                }
            },
            rows=[],
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    if not dr_br_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-DR-BR-01"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFNWT01WeightPolicyPruningTableRecord(
            schema="OV-FN-WT-01_fn01_weight_policy_pruning_table/v1",
            date=str(date),
            observable_id="OV-FN-WT-01",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": True,
                },
                "OV-DR-BR-01": {
                    "expected_path": str(default_dr_br),
                    "path": str(dr_br_path),
                    "present": False,
                },
            },
            rows=[],
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    if not br_fn_path.exists():
        status = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-BR-FN-01"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFNWT01WeightPolicyPruningTableRecord(
            schema="OV-FN-WT-01_fn01_weight_policy_pruning_table/v1",
            date=str(date),
            observable_id="OV-FN-WT-01",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": True,
                },
                "OV-DR-BR-01": {
                    "expected_path": str(default_dr_br),
                    "path": str(dr_br_path),
                    "present": True,
                },
                "OV-BR-FN-01": {
                    "expected_path": str(default_br_fn),
                    "path": str(br_fn_path),
                    "present": False,
                },
            },
            rows=[],
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    if not decl_path.exists():
        status = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-FN-WT-00"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFNWT01WeightPolicyPruningTableRecord(
            schema="OV-FN-WT-01_fn01_weight_policy_pruning_table/v1",
            date=str(date),
            observable_id="OV-FN-WT-01",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": True,
                },
                "OV-BR-FN-01": {
                    "expected_path": str(default_br_fn),
                    "path": str(br_fn_path),
                    "present": True,
                },
                "OV-DR-BR-01": {
                    "expected_path": str(default_dr_br),
                    "path": str(dr_br_path),
                    "present": True,
                },
                "OV-FN-WT-00": {
                    "expected_path": str(default_decl),
                    "path": str(decl_path),
                    "present": False,
                },
            },
            rows=[],
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    required_gates = ["CT01", "SYM01", "CAUS01"]
    gate_check = check_required_gates(
        repo_root=repo_root,
        required_gate_ids=required_gates,
        manifest_path=admissibility_manifest_path,
    )

    status: dict[str, Any] = {
        "blocked": bool(gate_check.blocked),
        "reasons": list(gate_check.reasons),
        "required_gates": list(required_gates),
        "admissibility_manifest": {
            "path": str(gate_check.manifest_path),
            "version": gate_check.manifest_version,
            "sha256": gate_check.manifest_sha256,
        },
    }

    computed_under_blocked_admissibility = bool(status.get("blocked"))

    residual_text = residual_path.read_text(encoding="utf-8")
    residual_sha = _sha256_text(residual_text)
    r_metric = _extract_fn01_r_metric(residual_text)

    dr_br_text = dr_br_path.read_text(encoding="utf-8")
    dr_br_locked = _extract_json_block(dr_br_text)
    dr_br_fp = _extract_record_fingerprint(dr_br_text)

    br_fn_text = br_fn_path.read_text(encoding="utf-8")
    br_fn_locked = _extract_json_block(br_fn_text)
    br_fn_fp = _extract_record_fingerprint(br_fn_text)

    decl_text = decl_path.read_text(encoding="utf-8")
    decl_locked = _extract_json_block(decl_text)
    decl_fp = _extract_record_fingerprint(decl_text)

    if bool((br_fn_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-BR-FN-01_is_blocked")

    if bool((dr_br_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-DR-BR-01_is_blocked")

    if bool((decl_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-FN-WT-00_is_blocked")

    if r_metric is None:
        status["blocked"] = True
        status["reasons"].append("fn01_residual_lock_missing_R_metric")

    computed_under_blocked_admissibility = bool(status.get("blocked"))

    fn_survivors = {
        str(r.get("candidate_id"))
        for r in list(br_fn_locked.get("rows") or [])
        if isinstance(r, dict) and r.get("survives_br_fn_constraints") == "true" and isinstance(r.get("candidate_id"), str)
    }

    br_status_by_id: dict[str, str] = {}
    for r in list(dr_br_locked.get("rows") or []):
        if not isinstance(r, dict):
            continue
        cid = r.get("candidate_id")
        st = r.get("survives_br01_constraints")
        if isinstance(cid, str) and isinstance(st, str):
            br_status_by_id[cid] = st

    br_survivors = sorted([cid for (cid, st) in br_status_by_id.items() if st == "true"])

    policy_rows = list(decl_locked.get("rows") or [])

    rows: list[dict[str, Any]] = []
    for pr in policy_rows:
        if not isinstance(pr, dict):
            continue
        policy_id = pr.get("policy_id")
        br_candidate_id = pr.get("br_candidate_id")
        fn_candidate_id = pr.get("fn_candidate_id")
        w_fn = pr.get("w_fn")
        max_score = pr.get("max_score")

        if not isinstance(policy_id, str) or not isinstance(br_candidate_id, str) or not isinstance(fn_candidate_id, str):
            continue
        if not isinstance(w_fn, (int, float)) or not isinstance(max_score, (int, float)):
            continue

        br_candidate_ids: list[str]
        if br_candidate_id == "*":
            # Wildcard policy: apply to every BR candidate surfaced in OV-DR-BR-01.
            br_candidate_ids = sorted(br_status_by_id.keys())
        else:
            br_candidate_ids = [br_candidate_id]

        for br_id in br_candidate_ids:
            reasons: list[str] = []
            out: SurvivalStatus = "unknown"
            score: float | None = None

            br_status = br_status_by_id.get(br_id)

            if br_status == "false":
                out = "false"
                reasons.append("br_candidate_failed_upstream_pruning")
            elif br_status == "unknown":
                out = "unknown"
                reasons.append("br_candidate_upstream_unknown")
            elif br_status is None:
                out = "unknown"
                reasons.append("br_candidate_not_in_OV-DR-BR-01")
            elif fn_candidate_id not in fn_survivors:
                out = "unknown"
                reasons.append("fn_candidate_not_survivor_from_OV-BR-FN-01")
            elif r_metric is None:
                out = "unknown"
                reasons.append("missing_R_metric")
            else:
                score = float(r_metric) * float(w_fn)
                if score <= float(max_score) + 0.0:
                    out = "true"
                    reasons.append("score_within_declared_max")
                else:
                    out = "false"
                    reasons.append("score_exceeds_declared_max")

            row = {
                "policy_id": str(policy_id),
                "br_candidate_id": str(br_id),
                "fn_candidate_id": str(fn_candidate_id),
                "w_fn": float(w_fn),
                "max_score": float(max_score),
                "r_metric": float(r_metric) if r_metric is not None else None,
                "score": float(score) if score is not None else None,
                "survives_fn_weight_policy_constraints": out,
                "computed_under_blocked_admissibility": bool(computed_under_blocked_admissibility),
                "reason_codes": reasons,
            }
            rows.append(row)

    if computed_under_blocked_admissibility:
        for r in rows:
            codes = list(r.get("reason_codes") or [])
            if "computed_under_blocked_admissibility" not in codes:
                codes.append("computed_under_blocked_admissibility")
            r["reason_codes"] = codes

    inputs = {
        "FN-01_cross_fit_metric_residual_DR02_DR03": {
            "path": str(residual_path),
            "present": True,
            "sha256": str(residual_sha),
            "r_metric": float(r_metric) if r_metric is not None else None,
        },
        "OV-DR-BR-01": {
            "path": str(dr_br_path),
            "schema": str(dr_br_locked.get("schema")),
            "locked_fingerprint": str(dr_br_fp),
            "record_fingerprint": str(dr_br_locked.get("fingerprint")),
            "present": True,
            "surviving_br_candidate_ids": list(br_survivors),
        },
        "OV-BR-FN-01": {
            "path": str(br_fn_path),
            "schema": str(br_fn_locked.get("schema")),
            "locked_fingerprint": str(br_fn_fp),
            "record_fingerprint": str(br_fn_locked.get("fingerprint")),
            "present": True,
            "surviving_fn_candidate_ids": sorted(fn_survivors),
        },
        "OV-FN-WT-00": {
            "path": str(decl_path),
            "schema": str(decl_locked.get("schema")),
            "locked_fingerprint": str(decl_fp),
            "record_fingerprint": str(decl_locked.get("fingerprint")),
            "present": True,
        },
    }

    return OVFNWT01WeightPolicyPruningTableRecord(
        schema="OV-FN-WT-01_fn01_weight_policy_pruning_table/v1",
        date=str(date),
        observable_id="OV-FN-WT-01",
        status=status,
        inputs=inputs,
        rows=rows,
        scope_limits=[
            "summary_only",
            "eliminative_only",
            "unknown_is_not_fail",
            "declared_threshold_application_only",
            "no_new_claims",
        ],
    )


def render_ovfnwt01_lock_markdown(record: OVFNWT01WeightPolicyPruningTableRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-FN-WT-01 — Pruning table (FN-01 weight policies; summary-only)\n\n"
        "Scope / limits\n"
        "- Summary-only / eliminative-only bookkeeping\n"
        "- Applies declared thresholds to a locked scalar (R_metric)\n"
        "- Unknown is not fail\n\n"
        "Notes\n"
        "- If an upstream declaration uses `br_candidate_id = \"*\"`, WT-01 expands it over all BR candidates\n"
        "- Expansion order is deterministic: BR candidate ids sorted lexicographically\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovfnwt01_lock(
    *,
    lock_path: Path | None = None,
    date: str = "2026-01-25",
    residual_lock_path: Path | None = None,
    br_fn_pruning_lock_path: Path | None = None,
    policy_decl_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-FN-WT-01_fn01_weight_policy_pruning_table.md"
        )

    rec = ovfnwt01_weight_policy_pruning_table_record(
        date=str(date),
        residual_lock_path=residual_lock_path,
        br_fn_pruning_lock_path=br_fn_pruning_lock_path,
        policy_decl_lock_path=policy_decl_lock_path,
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovfnwt01_lock_markdown(rec), encoding="utf-8")
    return out
