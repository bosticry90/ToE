from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION_STAGE_3_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION_STAGE_3_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_three_scope_and_lineages() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_3_OPEN_ONLY"
    )
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "fe74ad24a6b899c00fccc0e5c10219f6a59c9f079349a893beaffc682c4d1b99"
        ),
        "canonical_target": "operationalize_toe_retained_ccft_mathematical_objects_v0",
        "semantic_stage_id": "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION",
        "stage_number": 3,
    }
    boundary = authority["authorized_lineage_boundary"]
    assert boundary["mathematical_entry_count"] == 33
    assert boundary["lineage_component_count"] == 9
    assert boundary["conflict_count"] == 4
    assert boundary["unresolved_relationship_count"] == 5
    assert boundary["preferred_formulation_selected"] is False


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_input_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_freezes_operational_status_and_record_contracts() -> None:
    authority = _read(AUTHORITY_PATH)
    statuses = set(authority["operational_status_vocabulary"])
    assert "OPERATIONALLY_DEFINED" in statuses
    assert "OPERATIONALLY_DEFINED_ONLY_AS_BOUNDED_SURROGATE" in statuses
    assert "KNOWN_PHYSICS_OR_GENERIC_WAVE_BASELINE" in statuses
    assert "BLOCKED_BY_MISSING_BEARER" in statuses
    assert "BLOCKED_BY_MISSING_MEASUREMENT_MAP" in statuses
    assert "CONFLICTING_OPERATIONAL_INTERPRETATIONS" in statuses
    fields = set(authority["required_operational_record_fields"])
    assert "candidate_physical_bearer" in fields
    assert "value_and_zero_value_meaning" in fields
    assert "units_and_dimensional_status" in fields
    assert "scale_and_domain" in fields
    assert "measurement_or_inference_channel" in fields
    assert "known_physics_comparator" in fields
    assert "adequacy_failure_condition" in fields


def test_authority_prohibits_selection_repair_construction_and_stage_four() -> None:
    authority = _read(AUTHORITY_PATH)
    prohibited = " ".join(authority["prohibited_work"])
    assert "select CP-NLSE" in prohibited
    assert "repair the conflicting" in prohibited
    assert "choose between the two chi dynamics" in prohibited
    assert "assume psi phi chi" in prohibited
    assert "derive or construct a CCFT action" in prohibited
    assert "claim LCRD" in prohibited
    assert "open Stage 4 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION_STAGE_3_OPEN"
    )
    assert review["operational_result_created"] is False
    assert review["minimal_core_or_preferred_formulation_selected"] is False
    assert review["ccft_model_or_physical_claim_established"] is False
    assert review["stage_3_scientific_result_created"] is False
    assert review["stage_4_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
