from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = RELEASE_ROOT / (
    "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_STAGE_4_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = RELEASE_ROOT / (
    "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_four_scope() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_4_OPEN_ONLY"
    )
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "e8bd8faac099a9b1c9e759bfae544bbe8eb56ad631959b369dc595b9f9901adf"
        ),
        "canonical_target": "select_or_reject_toe_minimal_closed_ccft_core_v0",
        "semantic_stage_id": "MINIMAL_CLOSED_CCFT_CORE_DECISION",
        "stage_number": 4,
    }


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_input_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_binds_surrogate_only_candidate_boundary() -> None:
    boundary = _read(AUTHORITY_PATH)["authorized_candidate_boundary"]
    assert boundary["stage_3_operational_record_count"] == 20
    assert boundary["bounded_surrogate_record_count"] == 5
    assert boundary["generic_or_known_physics_record_count"] == 6
    assert boundary["fully_physically_operational_object_count"] == 0
    assert boundary["combined_wave_rotor_candidate_authorized"] is False
    assert boundary["preferred_formulation_selected"] is False
    assert boundary["minimal_core_selected"] is False


def test_authority_requires_closed_surrogate_contract_without_construction() -> None:
    authority = _read(AUTHORITY_PATH)
    fields = set(authority["closure_matrix_fields"])
    assert "complete_state_specification" in fields
    assert "closed_evolution_rule" in fields
    assert "initial_data_contract" in fields
    assert "parameter_contract" in fields
    assert "surrogate_operational_output" in fields
    assert "internal_failure_conditions" in fields
    prohibited = " ".join(authority["prohibited_work"])
    assert "invent a physical coherence bearer" in prohibited
    assert "combine CP-NLSE UCFF chi rotor" in prohibited
    assert "construct or vary an action" in prohibited
    assert "claim a selected numerical surrogate is a physical CCFT theory" in prohibited
    assert "open Stage 5 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_MINIMAL_CLOSED_CCFT_SURROGATE_CORE_DECISION_STAGE_4_OPEN"
    )
    assert review["core_selection_result_created"] is False
    assert review["minimal_core_selected"] is False
    assert review["physical_ccft_model_or_claim_established"] is False
    assert review["stage_4_scientific_result_created"] is False
    assert review["stage_5_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
