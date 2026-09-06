from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    CENSUS_PROGRAM_ID,
    PROGRAMS_KEY,
    scope_hash,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_STAGE_1_OPEN_AUTHORITY_20260730_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_STAGE_1_OPEN_AUTHORITY_REVIEW_20260730_v0.json"
)
MANIFEST_PATH = (
    RELEASE_ROOT
    / "bounded_program_manifests"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_MANIFEST_v1.json"
)
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_manifest_stage_one_exactly() -> None:
    authority = _read(AUTHORITY_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = manifest["stages"][0]
    bound = authority["authorized_stage"]
    assert bound["stage_number"] == stage["stage_number"] == 1
    assert bound["semantic_stage_id"] == stage["semantic_stage_id"]
    assert bound["canonical_target"] == stage["canonical_target"]
    assert bound["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert scope_hash(stage["canonical_scope"]) == stage["canonical_scope_hash"]
    assert authority["terminal_outcomes"] == stage[
        "mandatory_terminal_outcomes"
    ]


def test_authority_binds_eight_noninterpretive_batches() -> None:
    authority = _read(AUTHORITY_PATH)
    batches = authority["authorized_batches"]
    assert [row["batch_id"] for row in batches] == [
        f"batch_{index:02d}" for index in range(1, 9)
    ]
    assert len({row["source_root_id"] for row in batches}) == 8
    assert authority["file_and_byte_limits"]["stage_1_claim_extraction_limit"] == 0
    assert authority["file_and_byte_limits"]["stage_1_deep_review_limit"] == 0
    assert authority["custody_and_portability"]["reddit_excluded"] is True
    assert authority["parser_and_hostile_content_contract"][
        "office_and_pdf"
    ] == "CONTENT_NOT_EXTRACTED_METADATA_ONLY"


def test_scanner_and_schema_hashes_are_current() -> None:
    authority = _read(AUTHORITY_PATH)
    infrastructure = authority["index_infrastructure"]
    for path_key, hash_key in (
        ("index_schema_path", "index_schema_sha256"),
        ("scanner_path", "scanner_sha256"),
    ):
        path = REPO_ROOT / infrastructure[path_key]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == infrastructure[
            hash_key
        ]


def test_review_accepts_only_stage_one_open_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1_OPEN"
    )
    assert all(review["checks"].values())
    assert "Stage 2 remains prohibited until Stage 1 closes." in review[
        "nonclaim_boundary"
    ]


def test_preopen_registry_remains_unopened_without_events() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["open_attempt_number"] is None
