from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RECORD_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "DORMANT_SOURCE_SANITATION_20260711_v0.json"
)
REMOVED_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "OperatorCore"
    / "AdmissibleOperators.lean"
)
EMPTY_SCRATCH_PATH = REPO_ROOT / "scratch" / "rl02_lock.diff"


def test_malformed_dormant_source_is_removed_with_provenance() -> None:
    record = json.loads(RECORD_PATH.read_text(encoding="utf-8"))
    removed = record["removed_source"]

    assert record["schema_id"] == "DORMANT_SOURCE_SANITATION_20260711_v0"
    assert record["status"] == "APPLIED_MALFORMED_DORMANT_SOURCE_AND_EMPTY_SCRATCH_REMOVED"
    assert removed["path"] == str(REMOVED_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert removed["prior_byte_count"] == 7
    assert removed["prior_sha256"] == hashlib.sha256(b"{\\rtf1}").hexdigest()
    assert removed["import_count_before_removal"] == 0
    assert removed["consumer_count_before_removal"] == 0
    assert not REMOVED_PATH.exists()

    empty = record["removed_zero_byte_scratch"]
    assert empty["path"] == "scratch/rl02_lock.diff"
    assert empty["prior_byte_count"] == 0
    assert empty["consumer_count_before_removal"] == 0
    assert empty["git_blob_object_id"] == "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
    assert not EMPTY_SCRATCH_PATH.exists()


def test_dormant_source_sanitation_is_nonpromotional() -> None:
    record = json.loads(RECORD_PATH.read_text(encoding="utf-8"))
    assert record["boundary"] == {
        "historical_snapshot_records_preserved": True,
        "live_target_rotated": False,
        "scientific_artifacts_modified": False,
        "scientific_claim_changed": False,
    }
