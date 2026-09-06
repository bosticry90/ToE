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
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CLAIM_EXTRACTION_STAGE_3_OPEN_AUTHORITY_20260730_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CLAIM_EXTRACTION_STAGE_3_OPEN_AUTHORITY_REVIEW_20260730_v0.json"
)
MANIFEST_PATH = (
    RELEASE_ROOT
    / "bounded_program_manifests"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_MANIFEST_v1.json"
)
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_manifest_stage_three_exactly() -> None:
    authority = _read(AUTHORITY_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = manifest["stages"][2]
    bound = authority["authorized_stage"]
    assert bound["stage_number"] == stage["stage_number"] == 3
    assert bound["semantic_stage_id"] == stage["semantic_stage_id"]
    assert bound["canonical_target"] == stage["canonical_target"]
    assert bound["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert scope_hash(stage["canonical_scope"]) == stage["canonical_scope_hash"]
    assert authority["terminal_outcomes"] == stage[
        "mandatory_terminal_outcomes"
    ]


def test_authority_hash_binds_closed_stage_two_inputs() -> None:
    authority = _read(AUTHORITY_PATH)
    binding = authority["stage_2_input_binding"]
    for path_key, hash_key in (
        ("result_path", "result_sha256"),
        ("result_review_path", "result_review_sha256"),
        ("validation_path", "validation_sha256"),
        ("close_event_path", "close_event_sha256"),
    ):
        path = REPO_ROOT / binding[path_key]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == binding[hash_key]
    result = _read(REPO_ROOT / binding["result_path"])
    assert result["terminal_outcome"] == binding["terminal_outcome"]
    assert result["selection"]["selected_file_count"] == 640
    assert len(result["exact_duplicate_groups"]) == 421
    assert len(result["established_relationships"]) == 35
    assert len(result["lineage_components"]) == 16
    assert len(result["unresolved_relationships"]) == 16
    assert all(value is False for value in result["nonclaim_boundary"].values())


def test_authority_is_bounded_claim_extraction_only() -> None:
    authority = _read(AUTHORITY_PATH)
    limits = authority["workload_limits"]
    assert limits["maximum_eligible_deep_review_files"] == 640
    assert limits["maximum_eligible_deep_review_bytes"] == 1073741824
    assert limits["maximum_files_per_hypothesis_domain"] == 64
    assert limits["maximum_files_per_source_lineage"] == 8
    assert limits["maximum_claims_per_file"] == 32
    assert limits["maximum_extracted_claims"] == 4096
    assert limits["maximum_total_extracted_text_bytes"] == 268435456
    assert limits["overflow_is_not_repository_claim_exhaustion"] is True
    assert authority["deterministic_extraction_rules"][
        "scientific_truth_adjudication"
    ] is False
    assert authority["mandatory_exit_conditions"][
        "repair_or_subsidiary_target_permitted"
    ] is False


def test_review_accepts_only_stage_three_open_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == "AUTHORIZE_STAGE_3_OPEN"
    assert all(review["checks"].values())
    assert "claim extraction and classification only" in review[
        "nonclaim_boundary"
    ]


def test_preopen_registry_is_closed_after_stage_two() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "CLOSED"
    assert program["current_stage_number"] == 2
    assert program["attempted_stage_ids"] == [
        "REPOSITORY_WIDE_SOURCE_CENSUS",
        "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
    ]
    assert program["last_closed_attempt_number"] == 2
    assert program["open_attempt_number"] is None
    assert len(program["events"]) == 4
    assert registry["current_projection_v0"]["current_target"] == (
        "extract_and_classify_toe_repository_wide_native_hypothesis_claims_v0"
    )
