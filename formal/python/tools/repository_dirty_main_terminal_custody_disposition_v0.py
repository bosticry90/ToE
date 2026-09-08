"""Freeze terminal custody dispositions for the preserved dirty-main manifest.

This tool is deliberately conservative.  It does not import any dirty-main
path into the accepted recovery lineage.  It verifies every preserved custody
object and applies only explicit, reviewed path-cohort rules.  An unrecognised
path is a hard error rather than an implicit manual-review or catch-all result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any


TERMINAL_DISPOSITIONS = {
    "APPROVED_FOR_CLEAN_INTEGRATION",
    "PRESERVED_NONCURRENT_RESEARCH",
    "PRESERVED_EXECUTION_EVIDENCE",
    "DETERMINISTIC_REGENERABLE_OUTPUT",
    "HISTORICAL_CUSTODY_ONLY",
    "EXCLUDED_TRANSIENT",
}

DELETED_ROOT_RECORDS = {
    "MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md",
    "PUBLIC_OVERVIEW.md",
    "TECHNICAL_REPOSITORY_GUIDE.md",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def classify_path(path: str, status: str) -> tuple[str, str, str]:
    """Return terminal disposition, rule id, and reviewed rationale."""

    if path in DELETED_ROOT_RECORDS and status == " D":
        return (
            "HISTORICAL_CUSTODY_ONLY",
            "tracked_root_deletion_marker_v0",
            "Preserve the deletion event and frozen HEAD blob as custody; the "
            "accepted lineage retains its independently reviewed current source.",
        )
    if path == "README.md" and status == " M":
        return (
            "PRESERVED_NONCURRENT_RESEARCH",
            "dirty_root_readme_noncurrent_v0",
            "The local README aggregates unenrolled scientific lanes and cannot "
            "replace the accepted recovery-lineage overview.",
        )
    if path.startswith(
        "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
    ):
        return (
            "PRESERVED_EXECUTION_EVIDENCE",
            "external_acquisition_evidence_v0",
            "Downloaded responses, source archives, and acquisition logs are "
            "preserved as execution evidence without becoming current inputs.",
        )
    if path.startswith("formal/output/"):
        return (
            "PRESERVED_EXECUTION_EVIDENCE",
            "unenrolled_execution_output_v0",
            "Local numerical and instrumented outputs are preserved as evidence "
            "of unenrolled executions and are not current authority artifacts.",
        )
    if path.startswith("formal/docs/release/"):
        return (
            "HISTORICAL_CUSTODY_ONLY",
            "dirty_release_surface_custody_only_v0",
            "Untracked release, selector, packet, and review surfaces may imply "
            "authority; preserve their exact custody but do not enroll them.",
        )
    if path.startswith(("formal/docs/lanes/", "formal/docs/paper/")):
        return (
            "PRESERVED_NONCURRENT_RESEARCH",
            "unenrolled_research_document_v0",
            "The research document belongs to a preserved post-registry or "
            "exploratory lane and has no current scientific authority.",
        )
    if path.startswith(("formal/python/tests/", "formal/python/tools/")):
        return (
            "PRESERVED_NONCURRENT_RESEARCH",
            "unenrolled_research_implementation_v0",
            "The implementation or test supports preserved, unenrolled research "
            "and is not imported into the recovered current control plane.",
        )
    if path.startswith("formal/toe_formal/"):
        return (
            "PRESERVED_NONCURRENT_RESEARCH",
            "unenrolled_formal_research_v0",
            "The Lean change belongs to preserved, unenrolled formal research; "
            "modified authority mirrors and aggregate imports cannot self-enroll.",
        )
    raise ValueError(f"no reviewed terminal custody rule for {path!r} ({status!r})")


def canonical_rows_root(rows: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        identity = {
            "custody_object": row["custody_object"],
            "disposition_rule": row["disposition_rule"],
            "head_blob_sha256": row["head_blob_sha256"],
            "path": row["path"],
            "source_sha256": row["source_sha256"],
            "status": row["status"],
            "terminal_disposition": row["terminal_disposition"],
        }
        digest.update(
            json.dumps(identity, sort_keys=True, separators=(",", ":")).encode(
                "utf-8"
            )
        )
        digest.update(b"\n")
    return digest.hexdigest()


def verify_and_dispose(
    *,
    source_manifest: Path,
    source_root: Path,
    custody_root: Path,
    expected_manifest_sha256: str,
    expected_audited_commit: str,
    expected_total: int,
) -> dict[str, Any]:
    manifest_bytes = source_manifest.read_bytes()
    manifest_sha256 = sha256_bytes(manifest_bytes)
    if manifest_sha256 != expected_manifest_sha256:
        raise ValueError(
            f"manifest SHA-256 {manifest_sha256} != {expected_manifest_sha256}"
        )
    manifest = json.loads(manifest_bytes)
    if manifest["audited_commit"] != expected_audited_commit:
        raise ValueError("audited commit does not match the frozen selection")
    entries = manifest["entries"]
    if len(entries) != expected_total:
        raise ValueError(f"expected {expected_total} entries, observed {len(entries)}")

    rows: list[dict[str, Any]] = []
    path_seen: set[str] = set()
    custody_objects_verified = 0
    live_paths_verified = 0
    for index, entry in enumerate(entries):
        path = entry["path"]
        if path in path_seen:
            raise ValueError(f"duplicate manifest path: {path}")
        path_seen.add(path)
        disposition, rule, rationale = classify_path(path, entry["status"])
        if disposition not in TERMINAL_DISPOSITIONS:
            raise ValueError(f"nonterminal disposition for {path}: {disposition}")

        live_path = source_root.joinpath(*path.split("/"))
        if entry["exists"]:
            if not live_path.is_file():
                raise ValueError(f"live path is missing or not regular: {path}")
            live_sha256 = sha256_file(live_path)
            if live_sha256 != entry["sha256"]:
                raise ValueError(f"live bytes changed after custody capture: {path}")
            custody_object_rel = entry["custody_object"]
            custody_sha256 = entry["sha256"]
        else:
            if live_path.exists():
                raise ValueError(f"deleted path unexpectedly exists: {path}")
            live_sha256 = None
            custody_object_rel = entry["head_blob_custody_object"]
            custody_sha256 = entry["head_blob_sha256"]
        live_paths_verified += 1

        custody_object = custody_root.joinpath(*custody_object_rel.split("/"))
        if not custody_object.is_file():
            raise ValueError(f"missing custody object for {path}: {custody_object_rel}")
        if sha256_file(custody_object) != custody_sha256:
            raise ValueError(f"custody object hash mismatch for {path}")
        custody_objects_verified += 1

        rows.append(
            {
                "index": index,
                "path": path,
                "status": entry["status"],
                "tracked": entry["tracked"],
                "original_classification": entry["classification"],
                "source_sha256": entry["sha256"],
                "head_blob_sha256": entry["head_blob_sha256"],
                "custody_object": custody_object_rel,
                "live_bytes_verified": True,
                "custody_object_verified": True,
                "terminal_disposition": disposition,
                "disposition_rule": rule,
                "reviewed_rationale": rationale,
                "current_authority_effect": "NONE",
                "current_scientific_authority_effect": "NONE",
                "approved_for_clean_integration": False,
                "integration_result": "NOT_APPLICABLE",
            }
        )

    counts = Counter(row["terminal_disposition"] for row in rows)
    rule_counts = Counter(row["disposition_rule"] for row in rows)
    if sum(counts.values()) != expected_total:
        raise AssertionError("terminal disposition count does not reconcile")
    if any(row["terminal_disposition"] == "MANUAL_REVIEW_REQUIRED" for row in rows):
        raise AssertionError("MANUAL_REVIEW_REQUIRED is not terminal")

    return {
        "schema_id": "DIRTY_MAIN_TERMINAL_CUSTODY_DISPOSITION_LEDGER_20260725_v0",
        "status": "DIRTY_MAIN_TERMINAL_CUSTODY_DISPOSITIONS_COMPLETE",
        "source": {
            "audited_commit": manifest["audited_commit"],
            "manifest_path": str(source_manifest).replace("\\", "/"),
            "manifest_sha256": manifest_sha256,
            "manifest_identity_root": manifest["identity"],
            "original_worktree_unchanged_at_capture": manifest[
                "original_worktree_unchanged"
            ],
        },
        "policy": {
            "unmatched_path_behavior": "FAIL_CLOSED",
            "dirty_main_imported": False,
            "scientific_or_authority_promotion": False,
            "manual_review_required_is_terminal": False,
            "approved_for_clean_integration_count": counts[
                "APPROVED_FOR_CLEAN_INTEGRATION"
            ],
        },
        "verification": {
            "manifest_entries": len(rows),
            "unique_paths": len(path_seen),
            "live_paths_or_absences_verified": live_paths_verified,
            "custody_objects_verified": custody_objects_verified,
            "manual_review_required_remaining": 0,
            "unmatched_paths": 0,
        },
        "terminal_disposition_counts": {
            key: counts[key] for key in sorted(TERMINAL_DISPOSITIONS)
        },
        "disposition_rule_counts": dict(sorted(rule_counts.items())),
        "entry_identity_root_sha256": canonical_rows_root(rows),
        "entries": rows,
        "scientific_posture": "B-BLOCKED",
        "v2_enrollment": "NOT_AUTHORIZED",
        "scientific_resumption": "NOT_AUTHORIZED",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--custody-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--expected-audited-commit", required=True)
    parser.add_argument("--expected-total", type=int, required=True)
    args = parser.parse_args()

    result = verify_and_dispose(
        source_manifest=args.source_manifest.resolve(),
        source_root=args.source_root.resolve(),
        custody_root=args.custody_root.resolve(),
        expected_manifest_sha256=args.expected_manifest_sha256,
        expected_audited_commit=args.expected_audited_commit,
        expected_total=args.expected_total,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
