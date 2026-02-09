"""OV-BR-FN-01: Pruning table for BR→FN downstream discriminator (structure-only).

Purpose
- Provide an explicit, deterministic pruning-table surface for the first
  downstream BR-01 consumer (FN cross-fit metric residual).
- Produces eliminations only by comparing declared prediction structure
  (OV-BR-FN-00) against a locked upstream discriminator report.

Scope / limits
- Summary-only / eliminative-only bookkeeping.
- Unknown is not fail.
- No numeric interpretation; only structural presence checks against the locked
  upstream report.
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


def _present_residual_fields_from_lock(md_text: str) -> set[str]:
    """Extract a set of structurally present fields from the FN residual lock.

    The upstream lock is a markdown evidence report, not a JSON record.
    This extractor is intentionally conservative: it only recognizes a small set
    of canonical field keys and marks them present if the expected line pattern
    appears.
    """

    patterns: dict[str, str] = {
        "g_tt_02": r"^\s*-\s*g_tt\^02\s*=\s*.+$",
        "g_tt_03": r"^\s*-\s*g_tt\^03\s*=\s*.+$",
        "epsilon": r"^\s*-\s*epsilon\s*=\s*.+$",
        "R_metric": r"^\s*-\s*R_metric\s*=\s*.+$",
        "W_FN": r"^\s*-\s*W\(FN\)\s*=\s*.+$",
        "Score": r"^\s*-\s*Score\s*=\s*.+$",
    }

    present: set[str] = set()
    for field, pat in patterns.items():
        if re.search(pat, md_text, flags=re.MULTILINE):
            present.add(field)

    return present


@dataclass(frozen=True)
class OVBRFN01MetricResidualPruningTableRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    candidate_source: dict[str, Any]
    rows: list[dict[str, Any]]

    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "candidate_source": dict(self.candidate_source),
            "rows": list(self.rows),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovbrfn01_metric_residual_pruning_table_record(
    *,
    date: str = "2026-01-25",
    residual_lock_path: Path | None = None,
    pred_decl_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVBRFN01MetricResidualPruningTableRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_residual = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "functionals"
        / "FN-01_cross_fit_metric_residual_DR02_DR03.md"
    )
    residual_path = (residual_lock_path or default_residual).resolve()

    default_pred = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md"
    )
    pred_path = (pred_decl_lock_path or default_pred).resolve()

    if not residual_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_input_lock_FN-01_cross_fit_metric_residual_DR02_DR03"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {
                "path": None,
                "version": None,
                "skipped": True,
            },
        }
        return OVBRFN01MetricResidualPruningTableRecord(
            schema="OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
            date=str(date),
            observable_id="OV-BR-FN-01",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": False,
                }
            },
            candidate_source={},
            rows=[],
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    if not pred_path.exists():
        status = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-BR-FN-00"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {
                "path": None,
                "version": None,
                "skipped": True,
            },
        }
        return OVBRFN01MetricResidualPruningTableRecord(
            schema="OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
            date=str(date),
            observable_id="OV-BR-FN-01",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": True,
                },
                "OV-BR-FN-00": {
                    "expected_path": str(default_pred),
                    "path": str(pred_path),
                    "present": False,
                },
            },
            candidate_source={},
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
    present_fields = _present_residual_fields_from_lock(residual_text)

    pred_text = pred_path.read_text(encoding="utf-8")
    pred_locked = _extract_json_block(pred_text)
    pred_fp = _extract_record_fingerprint(pred_text)

    if bool((pred_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-BR-FN-00_is_blocked")

    # Candidate IDs are defined by the declaration record surface.
    candidate_rows = list(pred_locked.get("rows") or [])
    candidate_ids: list[str] = []
    pred_by_id: dict[str, dict[str, Any]] = {}
    for row in candidate_rows:
        if not isinstance(row, dict):
            continue
        cid = row.get("candidate_id")
        if isinstance(cid, str):
            candidate_ids.append(cid)
        if isinstance(cid, str) and isinstance(row.get("prediction"), dict):
            pred_by_id[cid] = dict(row.get("prediction") or {})

    candidate_ids = sorted(set(candidate_ids))

    rows: list[dict[str, Any]] = []
    for cid in candidate_ids:
        pred = pred_by_id.get(cid) or {}
        kind = pred.get("kind")

        status_out: SurvivalStatus = "unknown"
        reasons: list[str] = []

        if kind == "fn01_metric_residual_fields_required":
            required_fields = list(pred.get("required_fields") or [])
            missing_fields = sorted({str(f) for f in required_fields if str(f) not in present_fields})
            if missing_fields:
                status_out = "false"
                reasons.append("missing_required_residual_fields")
                reasons.append("missing_fields:" + ",".join(missing_fields))
            else:
                status_out = "true"
                reasons.append("declared_residual_structure_satisfied")
        else:
            status_out = "unknown"
            reasons.append("no_formal_residual_prediction_declared")

        rows.append(
            {
                "candidate_id": str(cid),
                "survives_br_fn_constraints": status_out,
                "computed_under_blocked_admissibility": bool(computed_under_blocked_admissibility),
                "reason_codes": reasons,
            }
        )

    if computed_under_blocked_admissibility:
        for r in rows:
            codes = list(r.get("reason_codes") or [])
            if "computed_under_blocked_admissibility" not in codes:
                codes.append("computed_under_blocked_admissibility")
            r["reason_codes"] = codes

    candidate_source = {
        "kind": "declared_surface",
        "source_lock": "OV-BR-FN-00",
        "path": str(pred_path),
        "row_key": "candidate_id",
    }

    inputs = {
        "FN-01_cross_fit_metric_residual_DR02_DR03": {
            "path": str(residual_path),
            "present": True,
            "sha256": str(residual_sha),
            "present_fields": sorted(present_fields),
        },
        "OV-BR-FN-00": {
            "path": str(pred_path),
            "schema": str(pred_locked.get("schema")),
            "locked_fingerprint": str(pred_fp),
            "record_fingerprint": str(pred_locked.get("fingerprint")),
            "present": True,
        },
    }

    return OVBRFN01MetricResidualPruningTableRecord(
        schema="OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
        date=str(date),
        observable_id="OV-BR-FN-01",
        status=status,
        inputs=inputs,
        candidate_source=candidate_source,
        rows=rows,
        scope_limits=[
            "summary_only",
            "eliminative_only",
            "no_numeric_interpretation",
            "no_new_claims",
            "unknown_is_not_fail",
            "structural_pruning_against_locked_report",
        ],
    )


def render_ovbrfn01_lock_markdown(record: OVBRFN01MetricResidualPruningTableRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-FN-01 — Pruning table (BR→FN cross-fit metric residual; summary-only)\n\n"
        "Scope / limits\n"
        "- Summary-only / eliminative-only bookkeeping\n"
        "- Uses the locked FN-01 cross-fit metric residual report as input\n"
        "- Unknown is not fail; candidates without declared predictions remain 'unknown'\n"
        "- No numeric interpretation; structural presence checks only\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbrfn01_lock(
    *,
    lock_path: Path | None = None,
    date: str = "2026-01-25",
    residual_lock_path: Path | None = None,
    pred_decl_lock_path: Path | None = None,
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
            / "OV-BR-FN-01_fn01_metric_residual_pruning_table.md"
        )

    rec = ovbrfn01_metric_residual_pruning_table_record(
        date=str(date),
        residual_lock_path=residual_lock_path,
        pred_decl_lock_path=pred_decl_lock_path,
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbrfn01_lock_markdown(rec), encoding="utf-8")
    return out
