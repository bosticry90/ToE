"""OV-DR-BR-00: BR-01 prediction declarations (structural lock).

Purpose
- Provide an explicit, schema-validated, hash-tracked declaration surface for
  BR-01 candidate prediction structures.
- Enables OV-DR-BR-01 to produce deterministic eliminations *only* by comparing
  declared prediction structures against locked OV-BR-05 values (no inference).

Scope / limits
- Structural bookkeeping only; no physics claim.
- Blocked-by-default if the declaration source file is missing.
- May be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).
"""

from __future__ import annotations

from dataclasses import dataclass
import ast
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.admissibility_manifest import check_required_gates


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


def _br01_candidate_ids(*, repo_root: Path) -> list[str]:
    cand_file = repo_root / "formal" / "python" / "toe" / "bridges" / "br01_candidates.py"
    tree = ast.parse(cand_file.read_text(encoding="utf-8"), filename=str(cand_file))

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name.startswith("BR01_"):
            names.add(node.name)

    return sorted(names)


def _validate_decl_schema(doc: dict[str, Any]) -> tuple[bool, str]:
    if doc.get("schema") != "BR01_prediction_declarations/v1":
        return False, "schema_unexpected"
    if not isinstance(doc.get("version"), int):
        return False, "version_not_int"
    cands = doc.get("candidates")
    if not isinstance(cands, dict):
        return False, "candidates_not_object"
    for k, v in cands.items():
        if not isinstance(k, str) or not k:
            return False, "candidate_id_invalid"
        if not isinstance(v, dict):
            return False, "candidate_entry_not_object"
        pred = v.get("prediction")
        if not isinstance(pred, dict):
            return False, "prediction_missing_or_not_object"
        kind = pred.get("kind")
        if kind not in {"none", "br05_structure_required"}:
            return False, "prediction_kind_unrecognized"
        if kind == "br05_structure_required":
            keys = pred.get("required_condition_keys")
            fields = pred.get("required_fields")
            if not isinstance(keys, list) or not all(isinstance(x, str) and x for x in keys):
                return False, "required_condition_keys_invalid"
            if not isinstance(fields, list) or not all(isinstance(x, str) and x for x in fields):
                return False, "required_fields_invalid"
    return True, "ok"


@dataclass(frozen=True)
class OVDRBR00BR01PredictionDeclarationsRecord:
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


def ovdrbr00_br01_prediction_declarations_record(
    *,
    date: str = "2026-01-25",
    declarations_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVDRBR00BR01PredictionDeclarationsRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_path = repo_root / "formal" / "python" / "toe" / "bridges" / "br01_prediction_declarations.json"
    decl_path = (declarations_path or default_path).resolve()

    # Missing-input blockers take precedence and short-circuit before any gate logic.
    if not decl_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_prediction_declarations_source"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {
                "path": None,
                "version": None,
                "skipped": True,
            },
        }
        return OVDRBR00BR01PredictionDeclarationsRecord(
            schema="OV-DR-BR-00_br01_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-DR-BR-00",
            status=status,
            inputs={
                "declarations": {
                    "expected_path": str(default_path),
                    "path": str(decl_path),
                    "present": False,
                }
            },
            rows=[],
            scope_limits=["blocked_by_missing_input", "blocked_by_default"],
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

    raw = decl_path.read_text(encoding="utf-8")
    raw_sha = _sha256_text(raw)

    try:
        doc = json.loads(raw)
    except json.JSONDecodeError:
        status["blocked"] = True
        status["reasons"].append("prediction_declarations_json_decode_error")
        return OVDRBR00BR01PredictionDeclarationsRecord(
            schema="OV-DR-BR-00_br01_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-DR-BR-00",
            status=status,
            inputs={
                "declarations": {
                    "expected_path": str(default_path),
                    "path": str(decl_path),
                    "present": True,
                    "raw_sha256": str(raw_sha),
                }
            },
            rows=[],
            scope_limits=["blocked_by_invalid_declaration_source"],
        )

    ok, reason = _validate_decl_schema(doc)
    if not ok:
        status["blocked"] = True
        status["reasons"].append("prediction_declarations_schema_invalid:" + str(reason))
        return OVDRBR00BR01PredictionDeclarationsRecord(
            schema="OV-DR-BR-00_br01_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-DR-BR-00",
            status=status,
            inputs={
                "declarations": {
                    "expected_path": str(default_path),
                    "path": str(decl_path),
                    "present": True,
                    "raw_sha256": str(raw_sha),
                    "schema": str(doc.get("schema")),
                    "version": doc.get("version"),
                }
            },
            rows=[],
            scope_limits=["blocked_by_invalid_declaration_source"],
        )

    br01_candidates = _br01_candidate_ids(repo_root=repo_root)
    declared = set((doc.get("candidates") or {}).keys())

    rows: list[dict[str, Any]] = []
    for cid in br01_candidates:
        entry = (doc.get("candidates") or {}).get(cid) or {}
        pred = (entry.get("prediction") or {}) if isinstance(entry, dict) else {}
        kind = pred.get("kind") if isinstance(pred, dict) else None
        rows.append(
            {
                "candidate_id": str(cid),
                "declared": bool(cid in declared),
                "prediction": dict(pred) if isinstance(pred, dict) else {},
                "prediction_kind": str(kind) if kind is not None else None,
            }
        )

    extras = sorted(declared - set(br01_candidates))

    inputs = {
        "declarations": {
            "expected_path": str(default_path),
            "path": str(decl_path),
            "present": True,
            "raw_sha256": str(raw_sha),
            "schema": str(doc.get("schema")),
            "version": doc.get("version"),
            "extra_candidate_ids": list(extras),
        }
    }

    if gate_check.blocked:
        return OVDRBR00BR01PredictionDeclarationsRecord(
            schema="OV-DR-BR-00_br01_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-DR-BR-00",
            status=status,
            inputs=inputs,
            rows=rows,
            scope_limits=[
                "structural_only",
                "hash_tracked_declaration_source",
                "no_new_claims",
                "blocked_by_admissibility_manifest",
                "requires_CT01_SYM01_CAUS01",
            ],
        )

    return OVDRBR00BR01PredictionDeclarationsRecord(
        schema="OV-DR-BR-00_br01_prediction_declarations/v1",
        date=str(date),
        observable_id="OV-DR-BR-00",
        status=status,
        inputs=inputs,
        rows=rows,
        scope_limits=[
            "structural_only",
            "hash_tracked_declaration_source",
            "no_new_claims",
        ],
    )


def render_ovdrbr00_lock_markdown(record: OVDRBR00BR01PredictionDeclarationsRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-DR-BR-00 — BR-01 prediction declarations (structural)\n\n"
        "Scope / limits\n"
        "- Structural-only declaration surface; no physics claim\n"
        "- Hash-tracks the declaration source file\n"
        "- Blocked-by-default if source missing\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovdrbr00_lock(
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
            / "OV-DR-BR-00_br01_prediction_declarations.md"
        )

    rec = ovdrbr00_br01_prediction_declarations_record(
        date=str(date),
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovdrbr00_lock_markdown(rec), encoding="utf-8")
    return out
