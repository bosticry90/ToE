from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY_STAGE_1_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY_STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_one_scope_and_requirements() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    )
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "297276852be0fed5e7dafdb9a90a3dc26a2807665665dbefc69dd8572b31fb19"
        ),
        "canonical_target": "inventory_toe_native_gravitational_requirements_v0",
        "semantic_stage_id": "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY",
        "stage_number": 1,
    }
    assert authority["requirement_ids"] == [
        "R1_DIMENSION",
        "R2_METRIC_ONLY",
        "R3_LOCALITY",
        "R4_DIFF_COVARIANCE",
        "R5_CK_FIREWALL",
        "R6_LOCAL_VARIATION",
        "R7_SOURCE_COMPATIBILITY",
        "R8_NEWTON_POISSON",
        "R9_MOMENTUM_CURRENT",
        "R10_STABILITY_NO_FIT",
    ]


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for source in authority["evidence_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_authority_prohibits_candidate_comparison_action_and_stage_two() -> None:
    authority = _read(AUTHORITY_PATH)
    prohibited = " ".join(authority["prohibited_work"])
    assert "rank or compare" in prohibited
    assert "select or promote" in prohibited
    assert "derive a new gravitational action" in prohibited
    assert "begin a gravitational calculation" in prohibited
    assert "open Stage 2 automatically" in prohibited


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == (
        "AUTHORIZE_NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY_STAGE_1_OPEN"
    )
    assert review["stage_1_scientific_result_created"] is False
    assert review["stage_2_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
