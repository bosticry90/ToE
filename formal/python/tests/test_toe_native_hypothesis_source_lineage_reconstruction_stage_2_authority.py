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
    / "TOE_NATIVE_HYPOTHESIS_SOURCE_LINEAGE_RECONSTRUCTION_STAGE_2_OPEN_AUTHORITY_20260730_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_HYPOTHESIS_SOURCE_LINEAGE_RECONSTRUCTION_STAGE_2_OPEN_AUTHORITY_REVIEW_20260730_v0.json"
)
MANIFEST_PATH = (
    RELEASE_ROOT
    / "bounded_program_manifests"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_MANIFEST_v1.json"
)
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_manifest_stage_two_exactly() -> None:
    authority = _read(AUTHORITY_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = manifest["stages"][1]
    bound = authority["authorized_stage"]
    assert bound["stage_number"] == stage["stage_number"] == 2
    assert bound["semantic_stage_id"] == stage["semantic_stage_id"]
    assert bound["canonical_target"] == stage["canonical_target"]
    assert bound["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert scope_hash(stage["canonical_scope"]) == stage["canonical_scope_hash"]
    assert authority["terminal_outcomes"] == stage[
        "mandatory_terminal_outcomes"
    ]


def test_authority_hash_binds_closed_stage_one_inputs() -> None:
    authority = _read(AUTHORITY_PATH)
    binding = authority["stage_1_input_binding"]
    for path_key, hash_key in (
        ("aggregate_manifest_path", "aggregate_manifest_sha256"),
        ("result_path", "result_sha256"),
        ("result_review_path", "result_review_sha256"),
        ("validation_path", "validation_sha256"),
        ("close_event_path", "close_event_sha256"),
    ):
        path = REPO_ROOT / binding[path_key]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == binding[hash_key]
    aggregate = _read(REPO_ROOT / binding["aggregate_manifest_path"])
    assert aggregate["aggregate_hash"] == binding["aggregate_hash"]
    assert aggregate["record_count"] == binding["record_count"] == 13563
    assert (
        aggregate["exact_duplicate_group_count"]
        == binding["exact_duplicate_group_count"]
        == 421
    )
    assert aggregate["scientific_lineage_conclusions_performed"] is False


def test_authority_is_lineage_only_and_bounded() -> None:
    authority = _read(AUTHORITY_PATH)
    limits = authority["workload_limits"]
    assert limits["maximum_bounded_source_comparison_files"] == 640
    assert limits["maximum_bounded_source_comparison_bytes"] == 1073741824
    assert limits["maximum_files_per_source_lineage"] == 8
    assert limits["maximum_unresolved_lineage_relationships"] == 512
    assert limits["maximum_claims_extracted"] == 0
    assert limits["maximum_evidence_promotions"] == 0
    assert authority["mandatory_exit_conditions"][
        "repair_or_subsidiary_target_permitted"
    ] is False
    assert authority["deterministic_lineage_rules"][
        "manual_preference_permitted"
    ] is False


def test_review_accepts_only_stage_two_open_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == "AUTHORIZE_STAGE_2_OPEN"
    assert all(review["checks"].values())
    assert "source-lineage reconstruction only" in review["nonclaim_boundary"]


def test_preopen_registry_is_closed_after_stage_one() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "CLOSED"
    assert program["current_stage_number"] == 1
    assert program["attempted_stage_ids"] == ["REPOSITORY_WIDE_SOURCE_CENSUS"]
    assert program["last_closed_attempt_number"] == 1
    assert program["open_attempt_number"] is None
    assert len(program["events"]) == 2
    assert registry["current_projection_v0"]["current_target"] == (
        "reconstruct_toe_native_hypothesis_source_lineages_v0"
    )
