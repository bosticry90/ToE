"""OV-FN-WT-00: FN-01 weight-policy declarations (structural lock).

Purpose
- Provide an explicit, schema-validated declaration surface for *weight policy*
  candidates that consume the FN-01 cross-fit metric residual report.
- Designed to be chained downstream of OV-BR-FN-01 (which selects FN candidate(s)).

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
    """Canonical FN candidate ID surface for FN-01 downstream records."""

    artifact_file = repo_root / "formal" / "python" / "toe" / "constraints" / "fn01_artifact.py"
    tree = ast.parse(artifact_file.read_text(encoding="utf-8"), filename=str(artifact_file))

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if node.name.startswith("fn01_make_") and node.name.endswith("_artifact"):
                names.add(node.name)

    return sorted(names)


def _br01_candidate_ids(*, repo_root: Path) -> list[str]:
    """Canonical BR candidate ID surface for weight-policy targeting."""

    cand_file = repo_root / "formal" / "python" / "toe" / "bridges" / "br01_candidates.py"
    tree = ast.parse(cand_file.read_text(encoding="utf-8"), filename=str(cand_file))

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name.startswith("BR01_"):
            names.add(node.name)

    return sorted(names)


def _validate_decl_schema(doc: dict[str, Any]) -> tuple[bool, str]:
    if doc.get("schema") != "FNWT01_weight_policy_declarations/v1":
        return False, "schema_unexpected"
    if not isinstance(doc.get("version"), int):
        return False, "version_not_int"

    cands = doc.get("candidates")
    if not isinstance(cands, dict):
        return False, "candidates_not_object"

    for policy_id, v in cands.items():
        if not isinstance(policy_id, str) or not policy_id:
            return False, "policy_id_invalid"
        if not isinstance(v, dict):
            return False, "policy_entry_not_object"

        fn_candidate_id = v.get("fn_candidate_id")
        if not isinstance(fn_candidate_id, str) or not fn_candidate_id:
            return False, "fn_candidate_id_invalid"

        # Optional: if absent, downstream interprets as wildcard ("*") over BR candidates.
        br_candidate_id = v.get("br_candidate_id")
        if br_candidate_id is not None and (not isinstance(br_candidate_id, str) or not br_candidate_id):
            return False, "br_candidate_id_invalid"

        w_fn = v.get("w_fn")
        max_score = v.get("max_score")
        if not isinstance(w_fn, (int, float)):
            return False, "w_fn_not_number"
        if not isinstance(max_score, (int, float)):
            return False, "max_score_not_number"

        if float(w_fn) <= 0.0:
            return False, "w_fn_not_positive"
        if float(max_score) < 0.0:
            return False, "max_score_negative"

    return True, "ok"


@dataclass(frozen=True)
class OVFNWT00WeightPolicyDeclarationsRecord:
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


def ovfnwt00_weight_policy_declarations_record(
    *,
    date: str = "2026-01-25",
    declarations_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVFNWT00WeightPolicyDeclarationsRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_path = repo_root / "formal" / "python" / "toe" / "bridges" / "fnwt01_weight_policy_declarations.json"
    decl_path = (declarations_path or default_path).resolve()

    if not decl_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_weight_policy_declarations_source"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {
                "path": None,
                "version": None,
                "skipped": True,
            },
        }
        return OVFNWT00WeightPolicyDeclarationsRecord(
            schema="OV-FN-WT-00_fn01_weight_policy_declarations/v1",
            date=str(date),
            observable_id="OV-FN-WT-00",
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
        status["reasons"].append("weight_policy_declarations_json_decode_error")
        return OVFNWT00WeightPolicyDeclarationsRecord(
            schema="OV-FN-WT-00_fn01_weight_policy_declarations/v1",
            date=str(date),
            observable_id="OV-FN-WT-00",
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
        status["reasons"].append("weight_policy_declarations_schema_invalid:" + str(reason))
        return OVFNWT00WeightPolicyDeclarationsRecord(
            schema="OV-FN-WT-00_fn01_weight_policy_declarations/v1",
            date=str(date),
            observable_id="OV-FN-WT-00",
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

    fn_candidate_ids = set(_fn01_artifact_constructor_ids(repo_root=repo_root))
    br_candidate_ids = set(_br01_candidate_ids(repo_root=repo_root))

    rows: list[dict[str, Any]] = []
    candidates = dict(doc.get("candidates") or {})
    for policy_id in sorted(candidates.keys()):
        entry = candidates.get(policy_id)
        if not isinstance(entry, dict):
            continue

        fn_candidate_id = str(entry.get("fn_candidate_id"))
        br_candidate_id_raw = entry.get("br_candidate_id")
        br_candidate_id = "*" if br_candidate_id_raw is None else str(br_candidate_id_raw)
        w_fn = float(entry.get("w_fn"))
        max_score = float(entry.get("max_score"))

        rows.append(
            {
                "policy_id": str(policy_id),
                "br_candidate_id": br_candidate_id,
                "fn_candidate_id": fn_candidate_id,
                "w_fn": w_fn,
                "max_score": max_score,
                "br_candidate_id_recognized": True if br_candidate_id == "*" else bool(br_candidate_id in br_candidate_ids),
                "fn_candidate_id_recognized": bool(fn_candidate_id in fn_candidate_ids),
            }
        )

    unknown_fn_candidate_ids = sorted(
        {str((v or {}).get("fn_candidate_id")) for v in candidates.values() if isinstance(v, dict)}
        - fn_candidate_ids
    )

    unknown_br_candidate_ids = sorted(
        {
            str((v or {}).get("br_candidate_id"))
            for v in candidates.values()
            if isinstance(v, dict) and (v.get("br_candidate_id") is not None)
        }
        - br_candidate_ids
        - {"*"}
    )

    inputs = {
        "declarations": {
            "expected_path": str(default_path),
            "path": str(decl_path),
            "present": True,
            "raw_sha256": str(raw_sha),
            "schema": str(doc.get("schema")),
            "version": doc.get("version"),
            "unknown_fn_candidate_ids": list(unknown_fn_candidate_ids),
            "unknown_br_candidate_ids": list(unknown_br_candidate_ids),
        }
    }

    scope_limits = [
        "structural_only",
        "hash_tracked_declaration_source",
        "no_new_claims",
    ]
    if gate_check.blocked:
        scope_limits.extend(["blocked_by_admissibility_manifest", "requires_CT01_SYM01_CAUS01"])

    return OVFNWT00WeightPolicyDeclarationsRecord(
        schema="OV-FN-WT-00_fn01_weight_policy_declarations/v1",
        date=str(date),
        observable_id="OV-FN-WT-00",
        status=status,
        inputs=inputs,
        rows=rows,
        scope_limits=scope_limits,
    )


def render_ovfnwt00_lock_markdown(record: OVFNWT00WeightPolicyDeclarationsRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-FN-WT-00 — FN-01 weight policy declarations (structural)\n\n"
        "Scope / limits\n"
        "- Structural-only declaration surface; no physics claim\n"
        "- Hash-tracks the declaration source file\n"
        "- Blocked-by-default if source missing\n\n"
        "Notes\n"
        "- `br_candidate_id` is optional; when omitted it is treated as wildcard `\"*\"` (apply to all BR candidates)\n"
        "- Wildcard semantics are deterministic and intended\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovfnwt00_lock(
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
            / "OV-FN-WT-00_fn01_weight_policy_declarations.md"
        )

    rec = ovfnwt00_weight_policy_declarations_record(
        date=str(date),
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovfnwt00_lock_markdown(rec), encoding="utf-8")
    return out
