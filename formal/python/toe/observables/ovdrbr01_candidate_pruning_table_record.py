"""OV-DR-BR-01: Candidate pruning table for DR-01 → BR-01 (summary-only lock).

Purpose
- Provide an explicit, deterministic pruning-table surface for the DR-01 → BR-01 loop.
- Uses OV-BR-05 as the *single canonical Bragg slope summary input*.

Scope / limits
- Summary-only / eliminative-only bookkeeping.
- No numeric interpretation and no new claims.
- If a candidate lacks a formally declared BR-01 low-k slope prediction structure,
  its status is "unknown" (not "fails").
- Blocked-by-default if OV-BR-05 lock is missing, and may be BLOCKED by
  admissibility manifest (CT01/SYM01/CAUS01).
"""

from __future__ import annotations

from dataclasses import dataclass, field
import ast
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Literal

from formal.python.toe.constraints.admissibility_manifest import check_required_gates


SurvivalStatus = Literal["true", "false", "unknown"]


def _empty_summary() -> dict[str, Any]:
    # Deterministic, schema-complete empty rollup for blocked/short-circuit branches.
    return {
        "counts": {"true": 0, "false": 0, "unknown": 0},
        "candidates": {"true": [], "false": [], "unknown": []},
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


def _br01_candidate_ids(*, repo_root: Path) -> list[str]:
    """Canonical BR-01 candidate ID surface: BR01_* function names.

    Source of truth: formal/python/toe/bridges/br01_candidates.py
    """

    cand_file = repo_root / "formal" / "python" / "toe" / "bridges" / "br01_candidates.py"
    tree = ast.parse(cand_file.read_text(encoding="utf-8"), filename=str(cand_file))

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name.startswith("BR01_"):
            names.add(node.name)

    return sorted(names)


@dataclass(frozen=True)
class OVDRBR01CandidatePruningTableRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    candidate_source: dict[str, Any]
    rows: list[dict[str, Any]]

    scope_limits: list[str]

    # Keep this at the end (defaulted field) so schema-completeness is enforced
    # without violating dataclass argument ordering rules.
    summary: dict[str, Any] = field(default_factory=_empty_summary)

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "candidate_source": dict(self.candidate_source),
            "summary": dict(self.summary),
            "rows": list(self.rows),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovdrbr01_candidate_pruning_table_record(
    *,
    date: str = "2026-01-25",
    br05_lock_path: Path | None = None,
    pred_decl_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVDRBR01CandidatePruningTableRecord:
    repo_root = _find_repo_root(Path(__file__))

    use_override_inputs = admissibility_manifest_path is not None

    default_br05 = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / ("OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md" if use_override_inputs else "OV-BR-05_bragg_lowk_slope_summary.md")
    )
    br05_path = (br05_lock_path or default_br05).resolve()

    default_pred = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / ("OV-DR-BR-00_br01_prediction_declarations_OVERRIDE.md" if use_override_inputs else "OV-DR-BR-00_br01_prediction_declarations.md")
    )
    pred_path = (pred_decl_lock_path or default_pred).resolve()

    # Missing-input blockers take precedence and short-circuit before any gate logic.
    if not br05_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-BR-05"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {
                "path": None,
                "version": None,
                "skipped": True,
            },
        }
        return OVDRBR01CandidatePruningTableRecord(
            schema="OV-DR-BR-01_candidate_pruning_table/v1",
            date=str(date),
            observable_id="OV-DR-BR-01",
            status=status,
            inputs={
                "OV-BR-05": {
                    "expected_path": str(default_br05),
                    "path": str(br05_path),
                    "present": False,
                }
            },
            candidate_source={},
            summary={
                "counts": {"true": 0, "false": 0, "unknown": 0},
                "candidates": {"true": [], "false": [], "unknown": []},
            },
            rows=[],
            scope_limits=[
                "blocked_by_missing_input_lock",
                "blocked_by_default",
            ],
        )

    if not pred_path.exists():
        status = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-DR-BR-00"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {
                "path": None,
                "version": None,
                "skipped": True,
            },
        }
        return OVDRBR01CandidatePruningTableRecord(
            schema="OV-DR-BR-01_candidate_pruning_table/v1",
            date=str(date),
            observable_id="OV-DR-BR-01",
            status=status,
            inputs={
                "OV-BR-05": {
                    "expected_path": str(default_br05),
                    "path": str(br05_path),
                    "present": True,
                },
                "OV-DR-BR-00": {
                    "expected_path": str(default_pred),
                    "path": str(pred_path),
                    "present": False,
                },
            },
            candidate_source={},
            summary={
                "counts": {"true": 0, "false": 0, "unknown": 0},
                "candidates": {"true": [], "false": [], "unknown": []},
            },
            rows=[],
            scope_limits=[
                "blocked_by_missing_input_lock",
                "blocked_by_default",
            ],
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

    lock_text = br05_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)
    br05_fp = _extract_record_fingerprint(lock_text)

    pred_text = pred_path.read_text(encoding="utf-8")
    pred_locked = _extract_json_block(pred_text)
    pred_fp = _extract_record_fingerprint(pred_text)

    # Structural pruning is allowed even when inputs are BLOCKED; we record this fact in status.
    if bool((locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-BR-05_is_blocked")

    if bool((pred_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-DR-BR-00_is_blocked")

    candidate_ids = _br01_candidate_ids(repo_root=repo_root)

    rows: list[dict[str, Any]] = []
    pred_by_id: dict[str, dict[str, Any]] = {}
    for row in list(pred_locked.get("rows") or []):
        if isinstance(row, dict) and isinstance(row.get("candidate_id"), str):
            pred_by_id[row["candidate_id"]] = dict(row.get("prediction") or {})

    br05_rows = list(locked.get("rows") or [])
    br05_by_condition: dict[str, dict[str, Any]] = {}
    for r in br05_rows:
        if isinstance(r, dict) and isinstance(r.get("condition_key"), str):
            br05_by_condition[str(r["condition_key"])] = r

    for cid in candidate_ids:
        pred = pred_by_id.get(cid) or {}
        kind = pred.get("kind")

        status_out: SurvivalStatus = "unknown"
        reasons: list[str] = []

        if kind == "br05_structure_required":
            required_keys = list(pred.get("required_condition_keys") or [])
            required_fields = list(pred.get("required_fields") or [])

            missing_keys = [k for k in required_keys if str(k) not in br05_by_condition]
            if missing_keys:
                status_out = "false"
                reasons.append("missing_required_br05_condition_keys")
                reasons.append("missing_keys:" + ",".join(sorted(map(str, missing_keys))))
            else:
                missing_fields: list[str] = []
                for k in required_keys:
                    row = br05_by_condition.get(str(k)) or {}
                    for f in required_fields:
                        if f not in row:
                            missing_fields.append(f"{k}:{f}")
                if missing_fields:
                    status_out = "false"
                    reasons.append("missing_required_br05_fields")
                    reasons.append("missing_fields:" + ",".join(sorted(missing_fields)))
                else:
                    status_out = "true"
                    reasons.append("declared_br05_structure_satisfied")
        else:
            status_out = "unknown"
            reasons.append("no_formal_br05_prediction_declared")

        rows.append(
            {
                "candidate_id": str(cid),
                "survives_br01_constraints": status_out,
                "reason_codes": reasons,
            }
        )

    # Deterministic, summary-only rollup for consumption by docs and downstream tooling.
    # This does not assert any numeric equivalence; it only counts/labels statuses.
    by_status: dict[SurvivalStatus, list[str]] = {"true": [], "false": [], "unknown": []}
    for r in rows:
        s = r.get("survives_br01_constraints")
        cid = r.get("candidate_id")
        if s in by_status and isinstance(cid, str):
            by_status[s].append(cid)

    summary = {
        "counts": {k: int(len(v)) for k, v in by_status.items()},
        "candidates": {k: list(v) for k, v in by_status.items()},
    }

    candidate_source = {
        "kind": "python_ast",
        "path": str(repo_root / "formal" / "python" / "toe" / "bridges" / "br01_candidates.py"),
        "function_prefix": "BR01_",
        "extraction_rule": "collect FunctionDef names with prefix; sorted lexicographically",
    }

    inputs = {
        "OV-BR-05": {
            "path": str(br05_path),
            "schema": str(locked.get("schema")),
            "locked_fingerprint": str(br05_fp),
            "record_fingerprint": str(locked.get("fingerprint")),
            "present": True,
        },
        "OV-DR-BR-00": {
            "path": str(pred_path),
            "schema": str(pred_locked.get("schema")),
            "locked_fingerprint": str(pred_fp),
            "record_fingerprint": str(pred_locked.get("fingerprint")),
            "present": True,
        },
    }

    return OVDRBR01CandidatePruningTableRecord(
        schema="OV-DR-BR-01_candidate_pruning_table/v1",
        date=str(date),
        observable_id="OV-DR-BR-01",
        status=status,
        inputs=inputs,
        candidate_source=candidate_source,
        summary=summary,
        rows=rows,
        scope_limits=[
            "summary_only",
            "eliminative_only",
            "no_numeric_interpretation",
            "no_new_claims",
            "unknown_is_not_fail",
            "structural_pruning_even_if_blocked",
        ],
    )


def render_ovdrbr01_lock_markdown(record: OVDRBR01CandidatePruningTableRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-DR-BR-01 — Candidate pruning table (DR-01 → BR-01; summary-only)\n\n"
        "Scope / limits\n"
        "- Summary-only / eliminative-only bookkeeping\n"
        "- Uses OV-BR-05 as the single canonical Bragg input\n"
        "- Unknown is not fail; candidates without declared predictions remain 'unknown'\n"
        "- No numeric interpretation; no new claims\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovdrbr01_lock(
    *,
    lock_path: Path | None = None,
    date: str = "2026-01-25",
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
            / "OV-DR-BR-01_candidate_pruning_table.md"
        )

    rec = ovdrbr01_candidate_pruning_table_record(
        date=str(date),
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovdrbr01_lock_markdown(rec), encoding="utf-8")
    return out
