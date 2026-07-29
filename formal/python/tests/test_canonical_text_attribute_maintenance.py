from __future__ import annotations

import json

import pytest

from formal.python.tools import canonical_text_attribute_maintenance as maintenance


def test_removed_rules_are_the_historical_tree_globs() -> None:
    assert maintenance.REMOVED_BROAD_RULES == (
        "formal/docs/release/*.json text eol=lf",
        "formal/docs/release/*.md text eol=lf",
        "formal/markdown/locks/**/*.md text eol=lf",
        "formal/output/*.json text eol=lf",
        "formal/output/**/*.json text eol=lf",
        "formal/python/**/*.py text eol=lf",
        "formal/toe_formal/**/*.lean text eol=lf",
    )


def test_prechange_inventory_covers_every_path_affected_by_removed_rules() -> None:
    report = json.loads(maintenance.PRECHANGE_PATH.read_text(encoding="utf-8"))
    paths = [row["path"] for row in report["paths"]]
    assert paths == maintenance.affected_paths()
    assert report["path_count"] == len(paths)
    assert report["boundary"]["bytes_rewritten"] is False
    assert report["boundary"]["index_renormalization_run"] is False


def test_postchange_preserves_all_index_objects_and_worktree_bytes() -> None:
    if not maintenance.POSTCHANGE_PATH.exists():
        pytest.skip("postchange verification is emitted only after the policy commit")
    report = json.loads(maintenance.POSTCHANGE_PATH.read_text(encoding="utf-8"))
    maintenance.validate_postchange(report)
    verification = report["verification"]
    assert verification["historical_index_objects_unchanged"] is True
    assert verification["historical_working_tree_bytes_unchanged"] is True
    assert verification["repository_wide_renormalization_run"] is False
    assert report["path_count"] == len(report["comparisons"])
