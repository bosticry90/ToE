from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_two_scope_and_selected_set() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_2_OPEN_ONLY"
    )
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "bf5a69abf0b8c49b1f5806afa6483a205201103126921af60fef6476348bb0e0"
        ),
        "canonical_target": "extract_toe_targeted_ccft_closure_contracts_v0",
        "semantic_stage_id": "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION",
        "stage_number": 2,
    }
    boundary = authority["contract_extraction_boundary"]
    assert boundary["selected_source_count"] == 96
    assert boundary["cp_nlse_selected_source_count"] == 48
    assert boundary["lcrd_v3_selected_source_count"] == 48
    assert boundary["selected_sources_git_portable_count"] == 96
    assert boundary["previously_deep_reviewed_selected_source_count"] == 0


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_input_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_freezes_checklists_classes_records_and_caps() -> None:
    authority = _read(AUTHORITY_PATH)
    assert len(authority["frozen_missing_contract_checklists"]["CP_NLSE"]) == 10
    assert len(authority["frozen_missing_contract_checklists"]["LCRD_V3"]) == 8
    assert len(authority["evidence_strength_vocabulary"]) == 7
    assert "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED" in authority[
        "evidence_strength_vocabulary"
    ]
    assert "NUMERICAL_DEFAULT_ONLY" in authority["evidence_strength_vocabulary"]
    assert "source_record_id_path_hash_lineage_and_custody" in authority[
        "required_contract_record_fields"
    ]
    assert authority["scientific_limits"]["maximum_source_bound_contract_records"] == 192
    assert authority["scientific_limits"]["targeted_content_search_pass_limit"] == 1


def test_authority_preserves_consumed_search_and_prohibits_construction() -> None:
    authority = _read(AUTHORITY_PATH)
    boundary = authority["contract_extraction_boundary"]
    assert boundary["content_search_passes_consumed"] == 1
    assert boundary["overflow_source_count"] == 137
    assert boundary["overflow_substitution_authorized"] is False
    prohibited = " ".join(authority["prohibited_work"])
    assert "consume a second content-search pass" in prohibited
    assert "substitute any of the 137 overflow paths" in prohibited
    assert "repair complete harmonize or choose" in prohibited
    assert "insert a new CCFT postulate" in prohibited
    assert "open Stage 3 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN"
    )
    assert review["contract_records_extracted"] == 0
    assert review["closure_contract_recovered_or_rejected"] is False
    assert review["new_content_search_authorized"] is False
    assert review["scientific_result_created"] is False
    assert review["stage_3_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
