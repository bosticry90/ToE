from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION_STAGE_2_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION_STAGE_2_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_two_scope_and_inventory() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_2_OPEN_ONLY"
    )
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "f2b412494409a17fa3527481c43a993a99f5e56b863b60c427a2746535c37902"
        ),
        "canonical_target": "reconstruct_toe_ccft_mathematical_lineages_and_conflicts_v0",
        "semantic_stage_id": "CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION",
        "stage_number": 2,
    }
    boundary = authority["authorized_inventory_boundary"]
    assert boundary["selected_source_count"] == 97
    assert boundary["mathematical_entry_count"] == 33
    assert boundary["conflicting_formulation_entry_count"] == 4


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_input_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_freezes_relationship_and_record_contracts() -> None:
    authority = _read(AUTHORITY_PATH)
    classes = set(authority["permitted_relationship_classes"])
    assert "EQUIVALENT_AFTER_CONVENTION_MAPPING" in classes
    assert "LIMIT_OR_APPROXIMATION_OF" in classes
    assert "DOMAIN_SPECIFIC_ALTERNATIVE" in classes
    assert "MATHEMATICALLY_INCOMPATIBLE" in classes
    assert "UNRESOLVED_RELATIONSHIP" in classes
    fields = set(authority["required_relationship_record_fields"])
    assert "units_dimensions_sign_and_normalization_comparison" in fields
    assert "domain_scale_initial_and_boundary_assumption_comparison" in fields
    assert "dependent_equations_and_approximation_level" in fields


def test_authority_prohibits_selection_repair_interpretation_and_stage_three() -> None:
    authority = _read(AUTHORITY_PATH)
    prohibited = " ".join(authority["prohibited_work"])
    assert "choose a preferred" in prohibited
    assert "repair incomplete equations" in prohibited
    assert "merge formulations without" in prohibited
    assert "assign operational or physical meaning" in prohibited
    assert "construct or select a representation" in prohibited
    assert "open Stage 3 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION_STAGE_2_OPEN"
    )
    assert review["ccft_lineage_result_created"] is False
    assert review["preferred_formulation_or_minimal_core_selected"] is False
    assert review["ccft_model_or_physical_claim_established"] is False
    assert review["stage_2_scientific_result_created"] is False
    assert review["stage_3_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
