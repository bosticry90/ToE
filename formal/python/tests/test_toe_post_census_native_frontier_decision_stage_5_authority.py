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
    / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_STAGE_5_OPEN_AUTHORITY_20260731_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_STAGE_5_OPEN_AUTHORITY_REVIEW_20260731_v0.json"
)
MANIFEST_PATH = (
    RELEASE_ROOT
    / "bounded_program_manifests"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_MANIFEST_v1.json"
)
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_manifest_stage_five_exactly() -> None:
    authority = _read(AUTHORITY_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = manifest["stages"][4]
    bound = authority["authorized_stage"]
    assert bound["stage_number"] == stage["stage_number"] == 5
    assert bound["semantic_stage_id"] == stage["semantic_stage_id"]
    assert bound["canonical_target"] == stage["canonical_target"]
    assert bound["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert scope_hash(stage["canonical_scope"]) == stage["canonical_scope_hash"]
    assert authority["terminal_outcomes"] == stage[
        "mandatory_terminal_outcomes"
    ]


def test_authority_hash_binds_closed_stage_four_inputs() -> None:
    authority = _read(AUTHORITY_PATH)
    binding = authority["stage_4_input_binding"]
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
    assert len(result["claim_reconciliation_records"]) == 2673
    assert result["native_hypothesis_graph"]["node_count"] == 3239
    assert result["native_hypothesis_graph"]["edge_count"] == 6822
    assert len(result["family_summaries"]) == 23
    assert result["status_counts"]["SUPPORTED_BUT_INCOMPLETE"] == 77
    assert result["candidate_canonical_promotion_dossiers"] == []
    assert result["nonclaim_boundary"][
        "repository_claim_exhaustion_established"
    ] is False
    close_event = _read(REPO_ROOT / binding["close_event_path"])
    assert close_event["event_hash"] == binding["close_event_hash"]


def test_authority_is_one_frontier_or_no_frontier_decision_only() -> None:
    authority = _read(AUTHORITY_PATH)
    limits = authority["workload_limits"]
    assert limits["maximum_candidate_families"] == 23
    assert limits["maximum_ranked_candidates"] == 23
    assert limits["maximum_selected_frontiers"] == 1
    assert limits["maximum_missing_prerequisites_per_candidate"] == 10
    assert authority["decision_contract"]["no_selection_is_valid"] is True
    assert authority["decision_contract"][
        "canonical_evidence_promotion"
    ] is False
    assert authority["decision_contract"][
        "automatic_next_program_open"
    ] is False
    assert authority["deterministic_ranking_contract"][
        "manual_preference_permitted"
    ] is False
    assert authority["mandatory_exit_conditions"][
        "repair_or_subsidiary_target_permitted"
    ] is False


def test_review_accepts_only_stage_five_open_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == "AUTHORIZE_STAGE_5_OPEN"
    assert all(review["checks"].values())
    assert "one next native research frontier" in review["nonclaim_boundary"]


def test_preopen_registry_is_closed_after_stage_four() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "CLOSED"
    assert program["current_stage_number"] == 4
    assert program["attempted_stage_ids"] == [
        "REPOSITORY_WIDE_SOURCE_CENSUS",
        "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
        "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
        "CURRENT_HYPOTHESIS_RECONCILIATION",
    ]
    assert program["last_closed_attempt_number"] == 4
    assert program["open_attempt_number"] is None
    assert len(program["events"]) == 8
    assert registry["current_projection_v0"]["current_target"] == (
        "select_toe_native_frontier_after_repository_wide_evidence_census_v0"
    )
