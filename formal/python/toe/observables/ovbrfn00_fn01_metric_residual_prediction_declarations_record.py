"""OV-BR-FN-00: FN metric-residual prediction declarations (structural lock).

Purpose
- Provide an explicit, schema-validated, hash-tracked declaration surface for the
  BR→FN downstream discriminator that consumes BR-01/MT-01 output.
- Enables OV-BR-FN-01 to produce deterministic eliminations *only* by comparing
  declared prediction structure against a locked upstream discriminator report.

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


def _fn01_artifact_constructor_ids(*, repo_root: Path) -> list[str]:
    """Canonical FN candidate ID surface for this loop.

    Source of truth: formal/python/toe/constraints/fn01_artifact.py

    Extraction rule: collect function names matching fn01_make_*_artifact.
    """

    artifact_file = repo_root / "formal" / "python" / "toe" / "constraints" / "fn01_artifact.py"
    tree = ast.parse(artifact_file.read_text(encoding="utf-8"), filename=str(artifact_file))

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if node.name.startswith("fn01_make_") and node.name.endswith("_artifact"):
                names.add(node.name)

    return sorted(names)


def _validate_decl_schema(doc: dict[str, Any]) -> tuple[bool, str]:
    if doc.get("schema") != "BRFN01_prediction_declarations/v1":
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
        if kind not in {"none", "fn01_metric_residual_fields_required"}:
            return False, "prediction_kind_unrecognized"
        if kind == "fn01_metric_residual_fields_required":
            fields = pred.get("required_fields")
            if not isinstance(fields, list) or not all(isinstance(x, str) and x for x in fields):
                return False, "required_fields_invalid"

    return True, "ok"


@dataclass(frozen=True)
class OVBRFN00MetricResidualPredictionDeclarationsRecord:
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


def ovbrfn00_metric_residual_prediction_declarations_record(
    *,
    date: str = "2026-01-25",
    declarations_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVBRFN00MetricResidualPredictionDeclarationsRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_path = repo_root / "formal" / "python" / "toe" / "bridges" / "brfn01_prediction_declarations.json"
    decl_path = (declarations_path or default_path).resolve()

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
        return OVBRFN00MetricResidualPredictionDeclarationsRecord(
            schema="OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-BR-FN-00",
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
        return OVBRFN00MetricResidualPredictionDeclarationsRecord(
            schema="OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-BR-FN-00",
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
        return OVBRFN00MetricResidualPredictionDeclarationsRecord(
            schema="OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1",
            date=str(date),
            observable_id="OV-BR-FN-00",
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

    candidate_ids = _fn01_artifact_constructor_ids(repo_root=repo_root)
    declared = set((doc.get("candidates") or {}).keys())

    rows: list[dict[str, Any]] = []
    for cid in candidate_ids:
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

    extras = sorted(declared - set(candidate_ids))

    inputs = {
        "declarations": {
            "expected_path": str(default_path),
            "path": str(decl_path),
            "present": True,
            "raw_sha256": str(raw_sha),
            "schema": str(doc.get("schema")),
            "version": doc.get("version"),
            "extra_candidate_ids": list(extras),
        },
        "candidate_source": {
            "kind": "python_ast",
            "path": str(repo_root / "formal" / "python" / "toe" / "constraints" / "fn01_artifact.py"),
            "function_prefix": "fn01_make_",
            "function_suffix": "_artifact",
            "extraction_rule": "collect FunctionDef names matching prefix+suffix; sorted lexicographically",
        },
    }

    scope_limits = [
        "structural_only",
        "hash_tracked_declaration_source",
        "no_new_claims",
    ]
    if gate_check.blocked:
        scope_limits.extend(["blocked_by_admissibility_manifest", "requires_CT01_SYM01_CAUS01"])

    return OVBRFN00MetricResidualPredictionDeclarationsRecord(
        schema="OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1",
        date=str(date),
        observable_id="OV-BR-FN-00",
        status=status,
        inputs=inputs,
        rows=rows,
        scope_limits=scope_limits,
    )


def render_ovbrfn00_lock_markdown(record: OVBRFN00MetricResidualPredictionDeclarationsRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-FN-00 — FN metric-residual prediction declarations (structural)\n\n"
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


def write_ovbrfn00_lock(
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
            / "OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md"
        )

    rec = ovbrfn00_metric_residual_prediction_declarations_record(
        date=str(date),
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbrfn00_lock_markdown(rec), encoding="utf-8")
    return out
