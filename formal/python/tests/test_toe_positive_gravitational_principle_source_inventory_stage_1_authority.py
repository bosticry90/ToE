from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY_STAGE_1_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY_STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
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
            "adec5050977697a470c1ef6afb4d136bc415f1a592008c9b7c2546a74f80ab90"
        ),
        "canonical_target": (
            "inventory_toe_positive_native_gravitational_principle_sources_v0"
        ),
        "semantic_stage_id": (
            "POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY"
        ),
        "stage_number": 1,
    }
    assert len(authority["authorized_source_set"]) == 10
    assert authority["inventory_limits"]["maximum_source_artifacts_for_deep_review"] == 128
    assert authority["inventory_limits"]["maximum_extracted_principle_statements"] == 256


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"] + authority["authorized_source_set"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_freezes_classification_and_provenance_contract() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["principle_status_vocabulary"] == [
        "POSITIVE_GENERATIVE_PRINCIPLE_CANDIDATE",
        "ACTION_CLASS_CONSTRAINING_PRINCIPLE_CANDIDATE",
        "EVALUATION_REQUIREMENT_ONLY",
        "KNOWN_PHYSICS_BASELINE",
        "ARCHITECTURAL_FIREWALL_ONLY",
        "HEURISTIC_OR_ANALOGY_ONLY",
        "BLOCKED_BY_MISSING_ONTOLOGY",
        "BLOCKED_BY_MISSING_SEAM_INPUT",
        "CONTRADICTED_OR_SUPERSEDED",
    ]
    assert "source_path" in authority["provenance_fields"]
    assert "source_sha256" in authority["provenance_fields"]
    assert "source_authority_status" in authority["provenance_fields"]
    assert "source_lineage" in authority["provenance_fields"]
    assert "supersession_status" in authority["provenance_fields"]


def test_authority_prohibits_principle_action_promotion_and_stage_two() -> None:
    authority = _read(AUTHORITY_PATH)
    prohibited = " ".join(authority["prohibited_work"])
    assert "adopt or derive" in prohibited
    assert "construct, select, vary, or calculate" in prohibited
    assert "promote Einstein-Hilbert" in prohibited
    assert "treat C_k as a physical action term" in prohibited
    assert "open Stage 2 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY_STAGE_1_OPEN"
    )
    assert review["stage_1_scientific_result_created"] is False
    assert review["native_gravitational_principle_selected_or_derived"] is False
    assert review["gravitational_action_constructed_or_selected"] is False
    assert review["gravitational_calculation_started"] is False
    assert review["stage_2_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
