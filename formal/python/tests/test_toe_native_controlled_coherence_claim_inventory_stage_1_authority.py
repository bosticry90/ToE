from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_CONTROLLED_COHERENCE_CLAIM_INVENTORY_STAGE_1_OPEN_AUTHORITY_20260729_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_CONTROLLED_COHERENCE_CLAIM_INVENTORY_STAGE_1_OPEN_AUTHORITY_REVIEW_20260729_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_stage_1_open_authority_binds_exact_inputs() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    )
    assert authority["semantic_stage_id"] == "CONTROLLED_COHERENCE_CLAIM_INVENTORY"
    assert authority["stage_1_target"] == (
        "inventory_toe_native_controlled_coherence_claims_v0"
    )
    assert len(authority["authorized_inputs"]) == 13
    for row in authority["authorized_inputs"]:
        path = REPO_ROOT / row["path"]
        assert path.is_file()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == row["sha256"]


def test_stage_1_open_authority_does_not_create_scientific_output() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["status"] == (
        "ACCEPTED_SEPARATE_SCIENTIFIC_OPEN_AUTHORITY_NO_STAGE_OUTPUT"
    )
    prohibitions = "\n".join(authority["prohibited_actions"])
    assert "No claim inventory producer may run before" in prohibitions
    assert "No representation, field, action, seam, pillar, observable" in prohibitions
    assert "No modification of the untracked reddit/ directory." in prohibitions
