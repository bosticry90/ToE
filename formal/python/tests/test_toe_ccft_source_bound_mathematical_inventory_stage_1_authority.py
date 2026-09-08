from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_STAGE_1_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
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
            "e348568927073147b6353de85f14a13c2e332f217677d8e7c16a0cc7cac0d53e"
        ),
        "canonical_target": "inventory_toe_source_bound_ccft_mathematical_structures_v0",
        "semantic_stage_id": "CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY",
        "stage_number": 1,
    }
    assert len(authority["authorized_source_set"]) == 10
    assert authority["inventory_limits"]["maximum_source_artifacts_for_deep_review"] == 160
    assert authority["inventory_limits"]["maximum_extracted_mathematical_statements"] == 1024


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_source_set"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_freezes_selection_classification_and_record_contracts() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["source_selection_contract"]["tie_breaking_rule"] == (
        "normalized custody-relative path then verified content hash"
    )
    assert authority["mathematical_content_vocabulary"] == [
        "EXPLICIT_CCFT_MATHEMATICS",
        "PARTIAL_MATHEMATICAL_STRUCTURE",
        "HEURISTIC_OR_ANALOGY",
        "CONFLICTING_CCFT_FORMULATION",
        "UNDEFINED_SYMBOL_OR_TERM",
        "CONTROL_OR_KNOWN_PHYSICS_IMPORT",
    ]
    assert "exact_source_path_and_hash" in authority["required_record_fields"]
    assert "units_or_dimensional_status" in authority["required_record_fields"]
    assert "physical_interpretation_status" in authority["required_record_fields"]


def test_authority_prohibits_interpretation_model_construction_and_stage_two() -> None:
    authority = _read(AUTHORITY_PATH)
    prohibited = " ".join(authority["prohibited_work"])
    assert "assign physical interpretation" in prohibited
    assert "choose or harmonize" in prohibited
    assert "invent missing definitions" in prohibited
    assert "select a scalar" in prohibited
    assert "construct an action" in prohibited
    assert "open Stage 2 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_STAGE_1_OPEN"
    )
    assert review["ccft_mathematical_inventory_created"] is False
    assert review["ccft_model_or_physical_claim_established"] is False
    assert review["representation_field_action_seam_or_observable_selected"] is False
    assert review["stage_1_scientific_result_created"] is False
    assert review["stage_2_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
