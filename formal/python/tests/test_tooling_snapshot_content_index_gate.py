from __future__ import annotations

import json

from formal.python.tools.tooling_snapshot_content_index import (
    OUTPUT_PATH,
    build_index,
    canonical_bytes,
)


def test_snapshot_content_index_matches_the_tracked_tree() -> None:
    expected = canonical_bytes(build_index())
    assert OUTPUT_PATH.read_bytes() == expected

    payload = json.loads(expected)
    metrics = payload["metrics"]
    assert metrics["tracked_snapshot_path_count"] >= metrics["unique_blob_count"]
    assert metrics["duplicate_group_count"] == len(payload["duplicate_groups"])
    assert metrics["redundant_worktree_bytes"] > 0


def test_snapshot_index_preserves_provenance_and_authorizes_no_deletion() -> None:
    payload = json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    assert payload["status"] == "INVENTORY_ONLY_PROVENANCE_PRESERVED_NO_DELETION_AUTHORIZED"
    assert payload["boundary"] == {
        "artifact_deletion_authorized": False,
        "authority_or_scientific_claim_changed": False,
        "content_addressed_migration_executed": False,
        "historical_paths_preserved": True,
    }
    assert len(payload["source_snapshot_tree_object_id"]) == 40
    assert "Git index/object database" in payload["source_tree_rule"]
