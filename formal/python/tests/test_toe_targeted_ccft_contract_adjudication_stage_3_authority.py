from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal/docs/release"
AUTHORITY = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_"
    "STAGE_3_OPEN_AUTHORITY_v0.json"
)
REVIEW = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_"
    "STAGE_3_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_three_scope() -> None:
    authority = _read(AUTHORITY)
    assert authority["status"] == "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_3_OPEN_ONLY"
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": "5b6cf39bbf3e4f8bf076dba1817778547410a8d7950164ce5b1c27d0f977410a",
        "canonical_target": "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0",
        "semantic_stage_id": "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
        "stage_number": 3,
    }


def test_authority_binds_all_fixed_records_and_exact_candidates() -> None:
    authority = _read(AUTHORITY)
    summary = authority["scientific_input_summary"]
    assert summary == {
        "checklist_items": 18,
        "conflicted_checklist_items": 3,
        "contract_records": 23,
        "exact_candidate_records": 7,
        "frozen_sources": 96,
        "new_source_search_authorized": False,
        "overflow_sources_available_to_stage_3": 0,
    }
    assert len(authority["exact_candidate_record_ids"]) == 7
    assert authority["conflict_preservation_boundary"]["selection_or_repair_authorized"] is False


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY)
    for binding in authority["authorized_input_bindings"] + authority["evidence_bindings"]:
        assert _sha(REPO_ROOT / binding["path"]) == binding["sha256"]


def test_authority_forbids_model_theorem_and_search_work() -> None:
    authority = _read(AUTHORITY)
    prohibited = " ".join(authority["prohibited_work"])
    assert "additional content-search pass" in prohibited
    assert "repair harmonize derive or select" in prohibited
    assert "insert a new CCFT postulate" in prohibited
    assert "open a theorem-discovery lane" in prohibited
    assert "open Stage 4 automatically" in prohibited


def test_review_accepts_authority_without_scientific_output() -> None:
    review = _read(REVIEW)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_STAGE_3_OPEN"
    )
    assert review["contract_adjudication_performed"] is False
    assert review["model_or_theorem_work_authorized"] is False
    assert review["scientific_result_created"] is False
    assert review["stage_4_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
