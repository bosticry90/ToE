from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CORRECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_ROUTE_SUBMISSION_CHECKPOINT_REFERENTIAL_INTEGRITY_CORRECTION_20260711_v0.json"
)
CURRENT_SURFACES = [
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md",
]


def _load() -> dict:
    return json.loads(CORRECTION_PATH.read_text(encoding="utf-8"))


def test_frozen_checkpoint_hashes_are_preserved_and_corrections_fail_closed() -> None:
    correction = _load()
    assert correction["status"] == "APPLIED_VERSIONED_CORRECTION_ORIGINAL_CHECKPOINTS_PRESERVED"
    assert len(correction["affected_checkpoints"]) == 3

    for row in correction["affected_checkpoints"]:
        path = REPO_ROOT / row["frozen_path"]
        assert path.exists()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == row["frozen_sha256"]
        if row["correction_kind"] == "missing_pointer_target":
            assert row["historical_asserted_value"] is True
            assert row["effective_pointer_complete"] is False
            assert "MISSING" in row["corrected_effective_status"]
        else:
            assert row["correction_kind"] == "downstream_dependency_invalidation"
            assert row["historical_asserted_value"] == (
                "EXTERNAL_SUBMISSION_PACKAGE_READY_BOUNDED"
            )
            assert row["effective_dependency_complete"] is False
            assert row["corrected_effective_status"] == (
                "NOT_AUTHORIZED_REFERENTIAL_INTEGRITY_CORRECTION_ACTIVE"
            )


def test_missing_pointer_is_not_fabricated_or_treated_as_complete() -> None:
    correction = _load()
    missing = correction["missing_pointer"]
    assert not (REPO_ROOT / missing["path"]).exists()
    assert missing == {
        "git_history_match_count": 0,
        "path": "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_PHYSICS_CONTRIBUTION_CLASSIFICATION_v0.md",
        "repository_object_name_match_count": 0,
        "worktree_exists": False,
    }
    assert correction["boundary"] == {
        "checkpoint_bytes_modified": False,
        "missing_document_fabricated": False,
        "scientific_claim_changed": False,
        "submission_or_publication_authorized": False,
    }


def test_effective_submission_posture_fails_closed_on_current_surfaces() -> None:
    correction = _load()
    posture = correction["effective_repository_posture"]
    assert posture == {
        "candidate_status": "BLOCKED_MISSING_PHYSICS_CONTRIBUTION_CLASSIFICATION_POINTER_TARGET",
        "package_status": "NOT_AUTHORIZED_REFERENTIAL_INTEGRITY_CORRECTION_ACTIVE",
        "readiness_status": "NOT_READY_MISSING_PUBLICATION_CONTRIBUTION_CLASSIFICATION_POINTER_TARGET",
    }

    combined = "\n".join(path.read_text(encoding="utf-8") for path in CURRENT_SURFACES)
    for status in posture.values():
        assert status in combined
    assert str(CORRECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/") in combined
