from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.loop_control_registry_integrity import load_registry


REPO_ROOT = find_repo_root(Path(__file__))
OUTPUT_PATH = REPO_ROOT / "formal/docs/release/TECHNICAL_DEBT_BASELINE_20260711_v0.json"
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
RETIREMENTS_PATH = (
    REPO_ROOT
    / "formal/docs/release/HISTORICAL_CURRENT_MIRROR_TEST_RETIREMENTS_20260711_v0.json"
)
AXIOM_LEDGER_PATH = REPO_ROOT / "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
SNAPSHOT_INDEX_PATH = (
    REPO_ROOT / "formal/docs/release/TOOLING_SNAPSHOT_CONTENT_INDEX_20260711_v0.json"
)
CUSTODY_PATH = REPO_ROOT / "formal/docs/release/PRESERVATION_BACKUP_CUSTODY_20260711_v0.json"
LEAN_ROOT = REPO_ROOT / "formal/toe_formal/ToeFormal"

SOURCE_COMMIT = "310b9dd426e3eea4585226467c4361f09104e6c8"
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"

AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE)
OPAQUE_RE = re.compile(r"^\s*opaque\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE)
DECLARATION_START_RE = re.compile(
    r"^\s*(?:axiom|theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)\s+",
    re.MULTILINE,
)


class BaselineError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BaselineError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)
    if not isinstance(value, dict):
        raise BaselineError(f"expected JSON object: {path}")
    return value


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _stable_id(prefix: str, identity: str) -> str:
    digest = hashlib.sha256(identity.encode("utf-8")).hexdigest()[:16].upper()
    return f"{prefix}-{digest}"


def _identity_set_sha256(identities: list[str]) -> str:
    return _sha256_bytes("\n".join(sorted(identities)).encode("utf-8"))


def _repo_path(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _strip_lean_comments(text: str) -> str:
    """Remove nested block and line comments while preserving positions/newlines."""
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if depth == 0 and text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                result.append(" ")
                index += 1
            continue
        if text.startswith("/-", index):
            depth += 1
            result.extend("  ")
            index += 2
            continue
        if depth > 0:
            if text.startswith("-/", index):
                depth -= 1
                result.extend("  ")
                index += 2
                continue
            result.append("\n" if text[index] == "\n" else " ")
            index += 1
            continue
        result.append(text[index])
        index += 1
    return "".join(result)


def _parse_axiom_ledger() -> dict[tuple[str, str], dict[str, Any]]:
    rows: dict[tuple[str, str], dict[str, Any]] = {}
    for line in AXIOM_LEDGER_PATH.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip().strip("`") for cell in line.strip().strip("|").split("|")]
        if len(cells) != 7:
            raise BaselineError(f"malformed axiom ledger row: {line}")
        declaration, file_path, status, reason, area, blocks, disposition = cells
        key = (file_path.replace("\\", "/"), declaration)
        if key in rows:
            raise BaselineError(f"duplicate axiom ledger key: {key}")
        if blocks not in {"yes", "no"}:
            raise BaselineError(f"invalid blocks_full_pillar_target value for {key}: {blocks}")
        rows[key] = {
            "status": status,
            "reason": reason,
            "associated_pillar_or_seam": area,
            "blocks_full_pillar_target": blocks == "yes",
            "replacement_or_discharge_path": disposition,
        }
    return rows


def _lean_declarations(
    pattern: re.Pattern[str], *, prefix: str, include_ledger: bool
) -> list[dict[str, Any]]:
    ledger = _parse_axiom_ledger() if include_ledger else {}
    declarations: list[dict[str, Any]] = []
    found_keys: set[tuple[str, str]] = set()
    for path in sorted(LEAN_ROOT.rglob("*.lean"), key=lambda item: item.as_posix().casefold()):
        text = path.read_text(encoding="utf-8")
        uncommented = _strip_lean_comments(text)
        rel = _repo_path(path)
        lines = text.splitlines()
        for match in pattern.finditer(uncommented):
            declaration = match.group(1)
            line_number = text.count("\n", 0, match.start()) + 1
            line_text = lines[line_number - 1].strip()
            next_declaration = DECLARATION_START_RE.search(uncommented, match.end())
            block_end = next_declaration.start() if next_declaration else len(text)
            declaration_block = text[match.start() : block_end].rstrip()
            identity = f"{rel}::{declaration}"
            row: dict[str, Any] = {
                "declaration": declaration,
                "declaration_block_sha256": _sha256_bytes(
                    declaration_block.encode("utf-8")
                ),
                "declaration_id": _stable_id(prefix, identity),
                "file": rel,
                "line": line_number,
                "statement_line_sha256": _sha256_bytes(line_text.encode("utf-8")),
            }
            if include_ledger:
                key = (rel, declaration)
                if key not in ledger:
                    raise BaselineError(f"axiom missing from ledger: {key}")
                row.update(ledger[key])
                found_keys.add(key)
            declarations.append(row)
    ids = [row["declaration_id"] for row in declarations]
    if len(ids) != len(set(ids)):
        raise BaselineError(f"stable {prefix} ID collision")
    if include_ledger and found_keys != set(ledger):
        missing = sorted(set(ledger) - found_keys)
        raise BaselineError(f"ledger rows do not match current axioms: {missing}")
    return declarations


def build_baseline() -> dict[str, Any]:
    registry_bytes = REGISTRY_PATH.read_bytes()
    registry = load_registry(REGISTRY_PATH)
    current_projection = registry["current_projection_v0"]
    current_target = current_projection["current_target"]
    if current_target != SCIENTIFIC_TARGET:
        raise BaselineError(
            f"scientific target changed: observed={current_target!r} expected={SCIENTIFIC_TARGET!r}"
        )

    retirements = _read_json(RETIREMENTS_PATH)
    retired_tests = retirements.get("retired_tests")
    if not isinstance(retired_tests, list):
        raise BaselineError("retirement ledger has no retired_tests array")
    assertions: list[dict[str, Any]] = []
    for row in retired_tests:
        if not isinstance(row, dict):
            raise BaselineError("retired test row is not an object")
        nodeid = str(row.get("nodeid", ""))
        failure_class = str(row.get("failure_class", ""))
        if not nodeid or not failure_class:
            raise BaselineError(f"invalid retired test row: {row}")
        assertions.append(
            {
                "assertion_id": _stable_id("QASSERT", nodeid),
                "failure_class": failure_class,
                "nodeid": nodeid,
            }
        )
    assertions.sort(key=lambda row: row["nodeid"])
    assertion_ids = [row["assertion_id"] for row in assertions]
    if len(assertion_ids) != len(set(assertion_ids)):
        raise BaselineError("stable quarantined-assertion ID collision")

    axioms = _lean_declarations(AXIOM_RE, prefix="AXIOM", include_ledger=True)
    opaques = _lean_declarations(OPAQUE_RE, prefix="OPAQUE", include_ledger=False)
    opaque_file_counts = Counter(row["file"] for row in opaques)

    snapshot_index = _read_json(SNAPSHOT_INDEX_PATH)
    snapshot_metrics = snapshot_index.get("metrics")
    if not isinstance(snapshot_metrics, dict):
        raise BaselineError("snapshot index has no metrics object")

    payload: dict[str, Any] = {
        "boundary": {
            "assertion_reclassification_authorized": False,
            "axiom_discharge_or_reclassification_authorized": False,
            "current_scientific_target_rotated": False,
            "git_history_rewrite_authorized": False,
            "opaque_definition_reclassification_authorized": False,
            "registry_sharding_or_monolith_retirement_executed": False,
            "scientific_claim_or_blocker_movement_authorized": False,
            "snapshot_deletion_or_rebinding_authorized": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "current_scientific_authority": {
            "current_target": current_target,
            "current_target_evidence": current_projection["current_target_evidence"],
            "current_target_report": current_projection["current_target_report"],
            "previous_target": current_projection["previous_target"],
        },
        "maintenance_program": {
            "lanes": [
                {
                    "lane_id": "registry_sharding_and_current_projection",
                    "priority": 1,
                    "status": "proposed_guardrail_preparation_pending_separate_authority",
                },
                {
                    "lane_id": "quarantined_assertion_reconciliation",
                    "priority": 2,
                    "status": "baseline_frozen_not_started",
                },
                {
                    "lane_id": "lean_axiom_and_opaque_definition_review",
                    "priority": 3,
                    "status": "baseline_frozen_not_started",
                },
                {
                    "lane_id": "snapshot_deduplication_and_retention_migration",
                    "priority": 4,
                    "status": "inventory_only_no_deletion_authorized",
                },
            ],
            "maintenance_target": MAINTENANCE_TARGET,
            "scientific_target_displacement": False,
        },
        "schema_id": "TECHNICAL_DEBT_BASELINE_20260711_v0",
        "source_commit": SOURCE_COMMIT,
        "status": "FROZEN_INVENTORY_ONLY_NO_REMEDIATION_OR_AUTHORITY_ROTATION",
        "technical_debt_baselines": {
            "lean_axioms": {
                "axiom_count": len(axioms),
                "axiom_file_count": len({row["file"] for row in axioms}),
                "axioms": axioms,
                "blocking_full_pillar_target_count": sum(
                    bool(row["blocks_full_pillar_target"]) for row in axioms
                ),
                "ledger_path": _repo_path(AXIOM_LEDGER_PATH),
                "ledger_sha256": _sha256_file(AXIOM_LEDGER_PATH),
                "stable_identity_set_sha256": _identity_set_sha256(
                    [row["declaration_id"] for row in axioms]
                ),
                "sorry_or_admit_count": 0,
            },
            "lean_opaque_definitions": {
                "candidate_count": len(opaques),
                "candidate_file_count": len(opaque_file_counts),
                "candidates": opaques,
                "classification_status": "UNREVIEWED_BASELINE_CANDIDATES",
                "file_counts": dict(sorted(opaque_file_counts.items())),
                "stable_identity_set_sha256": _identity_set_sha256(
                    [row["declaration_id"] for row in opaques]
                ),
            },
            "loop_control_registry": {
                "active_workstream_count": registry["active_workstream_count"],
                "casefold_alias_row_count": len(registry["casefold_key_aliases_v0"]),
                "current_target_state_authoritative_key_count": len(
                    registry["current_target_state_authority_contract_v0"][
                        "authoritative_keys"
                    ]
                ),
                "current_target_state_compatibility_key_count": registry[
                    "current_target_state_authority_contract_v0"
                ]["flattened_compatibility_key_count"],
                "current_target_state_key_count": len(registry["current_target_state"]),
                "duplicate_workstream_extra_record_count": sum(
                    row["occurrence_count"] - 1
                    for row in registry["duplicate_workstream_id_quarantine_v0"][
                        "collisions"
                    ]
                ),
                "duplicate_workstream_id_group_count": registry[
                    "duplicate_workstream_id_quarantine_v0"
                ]["collision_count"],
                "path": _repo_path(REGISTRY_PATH),
                "schema_id": registry["schema_id"],
                "sha256": _sha256_bytes(registry_bytes),
                "size_bytes": len(registry_bytes),
                "size_mib": round(len(registry_bytes) / (1024 * 1024), 6),
                "status_counts": dict(
                    sorted(Counter(str(row.get("status", "")) for row in registry["workstreams"]).items())
                ),
                "top_level_key_count": len(registry),
                "unique_workstream_id_count": len(
                    {str(row["workstream_id"]) for row in registry["workstreams"]}
                ),
                "workstream_record_count": len(registry["workstreams"]),
            },
            "quarantined_assertions": {
                "assertion_count": len(assertions),
                "assertions": assertions,
                "failure_class_counts": dict(
                    sorted(Counter(row["failure_class"] for row in assertions).items())
                ),
                "referenced_test_file_count": len(
                    {row["nodeid"].split("::", 1)[0] for row in assertions}
                ),
                "source_ledger_path": _repo_path(RETIREMENTS_PATH),
                "source_ledger_sha256": _sha256_file(RETIREMENTS_PATH),
                "stable_identity_set_sha256": _identity_set_sha256(assertion_ids),
            },
            "tooling_snapshots": {
                "inventory_boundary": snapshot_index["boundary"],
                "duplicate_group_count": snapshot_metrics["duplicate_group_count"],
                "inventory_path": _repo_path(SNAPSHOT_INDEX_PATH),
                "inventory_sha256": _sha256_file(SNAPSHOT_INDEX_PATH),
                "inventory_status": snapshot_index["status"],
                "redundant_worktree_bytes": snapshot_metrics["redundant_worktree_bytes"],
                "redundant_worktree_mib": round(
                    snapshot_metrics["redundant_worktree_bytes"] / (1024 * 1024), 6
                ),
                "source_snapshot_tree_object_id": snapshot_index[
                    "source_snapshot_tree_object_id"
                ],
                "tracked_snapshot_bytes": snapshot_metrics["tracked_snapshot_bytes"],
                "tracked_snapshot_path_count": snapshot_metrics[
                    "tracked_snapshot_path_count"
                ],
                "unique_blob_count": snapshot_metrics["unique_blob_count"],
            },
        },
        "verification_contract": {
            "count_or_identity_change_requires_versioned_packet": True,
            "local_preservation_custody_path": _repo_path(CUSTODY_PATH),
            "local_preservation_custody_sha256": _sha256_file(CUSTODY_PATH),
            "off_device_preservation_required_for_current_maintenance_phase": False,
            "preservation_scope": "same_volume_only_total_C_drive_loss_not_covered_and_risk_accepted",
            "stable_id_rule": "uppercase prefix plus first 16 hex characters of SHA-256 over the canonical identity",
        },
    }
    return payload


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the frozen technical-debt baseline.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="Write the canonical baseline artifact.")
    mode.add_argument("--check", action="store_true", help="Verify the checked-in artifact.")
    args = parser.parse_args()

    data = canonical_json_bytes(build_baseline())
    if args.check:
        if not OUTPUT_PATH.exists():
            raise BaselineError(f"baseline artifact is missing: {OUTPUT_PATH}")
        if OUTPUT_PATH.read_bytes() != data:
            raise BaselineError("technical-debt baseline differs from current frozen inventory")
        print(f"technical_debt_baseline: OK sha256={_sha256_bytes(data)}")
        return 0

    _atomic_write(OUTPUT_PATH, data)
    print(f"technical_debt_baseline: wrote {OUTPUT_PATH} sha256={_sha256_bytes(data)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
