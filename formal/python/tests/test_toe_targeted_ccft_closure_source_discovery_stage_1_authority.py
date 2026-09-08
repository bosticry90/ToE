from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
    "STAGE_1_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
    "STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_one_scope_and_source_set() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    )
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "d2019a5d75347897cf4648ec88945b2a4cc2209be10ececf6e6c5b7f33d5d6aa"
        ),
        "canonical_target": "discover_toe_targeted_ccft_closure_evidence_sources_v0",
        "semantic_stage_id": "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY",
        "stage_number": 1,
    }
    assert len(authority["authorized_source_set"]) == 7
    assert authority["scientific_limits"]["authorized_source_root_count"] == 8
    assert authority["scientific_limits"]["maximum_deep_review_files"] == 96


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_source_set"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_freezes_one_pass_selection_and_candidate_contract() -> None:
    authority = _read(AUTHORITY_PATH)
    selection = authority["selection_contract"]
    assert selection["automatic_second_search"] is False
    assert selection["content_extraction_during_stage_1"] is False
    assert selection["selected_content_passes_consumed_during_stage_1"] == 0
    assert selection["desired_model_or_recovery_outcome_may_affect_selection"] is False
    assert "content_sha256_or_git_blob_identity" in authority[
        "required_candidate_record_fields"
    ]
    assert "exact_duplicate_group" in authority["required_candidate_record_fields"]


def test_authority_prohibits_contract_adjudication_repair_and_stage_two() -> None:
    prohibited = " ".join(_read(AUTHORITY_PATH)["prohibited_work"])
    assert "declare a missing contract recovered" in prohibited
    assert "extract or adjudicate" in prohibited
    assert "repair harmonize or select" in prohibited
    assert "insert a new CCFT postulate" in prohibited
    assert "open Stage 2 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_OPEN"
    )
    assert review["archive_or_repository_content_searched"] is False
    assert review["candidate_source_set_created"] is False
    assert review["closure_contract_recovered_or_rejected"] is False
    assert review["scientific_result_created"] is False
    assert review["stage_2_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
