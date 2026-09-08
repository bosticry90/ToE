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
    / "TOE_CURRENT_NATIVE_HYPOTHESIS_EVIDENCE_RECONCILIATION_STAGE_4_OPEN_AUTHORITY_20260730_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_CURRENT_NATIVE_HYPOTHESIS_EVIDENCE_RECONCILIATION_STAGE_4_OPEN_AUTHORITY_REVIEW_20260730_v0.json"
)
MANIFEST_PATH = (
    RELEASE_ROOT
    / "bounded_program_manifests"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_MANIFEST_v1.json"
)
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_manifest_stage_four_exactly() -> None:
    authority = _read(AUTHORITY_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = manifest["stages"][3]
    bound = authority["authorized_stage"]
    assert bound["stage_number"] == stage["stage_number"] == 4
    assert bound["semantic_stage_id"] == stage["semantic_stage_id"]
    assert bound["canonical_target"] == stage["canonical_target"]
    assert bound["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert scope_hash(stage["canonical_scope"]) == stage["canonical_scope_hash"]
    assert authority["terminal_outcomes"] == stage[
        "mandatory_terminal_outcomes"
    ]


def test_authority_hash_binds_closed_stage_three_inputs() -> None:
    authority = _read(AUTHORITY_PATH)
    binding = authority["stage_3_input_binding"]
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
    summary = result["source_review_summary"]
    assert summary["selected_source_count"] == 640
    assert summary["passive_text_parsed_source_count"] == 611
    assert result["source_bound_claim_count"] == 2673
    assert summary["sources_with_extracted_claims"] == 408
    assert summary["exact_duplicate_alias_count"] == 28
    assert result["unreviewed_overflow_counts"][
        "stage_1_records_outside_bounded_stage_3_selection"
    ] == 12923
    close_event = _read(REPO_ROOT / binding["close_event_path"])
    assert close_event["event_hash"] == binding["close_event_hash"]


def test_authority_is_bounded_reconciliation_only() -> None:
    authority = _read(AUTHORITY_PATH)
    limits = authority["workload_limits"]
    assert limits["input_claim_count"] == 2673
    assert limits["maximum_graph_nodes"] == 4096
    assert limits["maximum_graph_edges"] == 16384
    assert limits["maximum_claims_per_reconciliation_cluster"] == 64
    assert limits["maximum_candidate_promotion_dossiers"] == 128
    assert limits["maximum_independent_promotion_reviews"] == 128
    assert limits["maximum_unresolved_relationships"] == 2048
    assert authority["deterministic_reconciliation_rules"][
        "truth_adjudication_permitted"
    ] is False
    assert authority["candidate_promotion_contract"][
        "promotion_decision_authorized"
    ] is False
    assert authority["mandatory_exit_conditions"][
        "repair_or_subsidiary_target_permitted"
    ] is False
    assert authority["edge_vocabulary"] == [
        "SUPPORTS",
        "CONTRADICTS",
        "REFINES",
        "SUPERSEDES",
        "DEPENDS_ON",
        "SEMANTIC_DUPLICATE_CANDIDATE",
        "USES_INCOMPATIBLE_ASSUMPTIONS",
        "HAS_MATHEMATICAL_SUPPORT",
        "HAS_CONCEPTUAL_SUPPORT_ONLY",
        "REMAINS_OPERATIONALLY_UNDEFINED",
    ]


def test_review_accepts_only_stage_four_open_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == "AUTHORIZE_STAGE_4_OPEN"
    assert all(review["checks"].values())
    assert "reconciliation only" in review["nonclaim_boundary"]


def test_preopen_registry_is_closed_after_stage_three() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "CLOSED"
    assert program["current_stage_number"] == 3
    assert program["attempted_stage_ids"] == [
        "REPOSITORY_WIDE_SOURCE_CENSUS",
        "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
        "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
    ]
    assert program["last_closed_attempt_number"] == 3
    assert program["open_attempt_number"] is None
    assert len(program["events"]) == 6
    assert registry["current_projection_v0"]["current_target"] == (
        "reconcile_toe_current_native_hypothesis_evidence_v0"
    )
