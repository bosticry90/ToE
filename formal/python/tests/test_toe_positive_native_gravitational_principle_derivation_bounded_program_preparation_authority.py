from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE
    / "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE
    / "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0.json"
)
TARGET = "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_the_closed_gravitational_survey() -> None:
    authority = _read(AUTHORITY_PATH)
    bound = authority["consumed_terminal_checkpoint"]
    for path_key, hash_key in (
        ("survey_closeout_result_path", "survey_closeout_result_sha256"),
        ("survey_closeout_review_path", "survey_closeout_review_sha256"),
    ):
        assert _sha256(REPO_ROOT / bound[path_key]) == bound[hash_key]
    assert bound["closeout_commit"] == "4665b86959587aa95c7cf3114a78b77dae3f566a"
    assert bound["selected_route"] == "DERIVE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE"


def test_authority_is_preparation_only() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["authority_decision"] == "AUTHORIZE_PROPOSAL_PREPARATION_ONLY"
    assert authority["authorized_target"] == TARGET
    assert authority["zero_scientific_execution"] is True
    prohibited = set(authority["prohibited_work"])
    assert "install the proposed program" in prohibited
    assert "open any scientific stage" in prohibited
    assert "select or endorse a native gravitational principle" in prohibited
    assert "perform a gravitational calculation" in prohibited


def test_independent_review_accepts_only_preparation_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == "ACCEPT_PROPOSAL_PREPARATION_AUTHORITY_ONLY"
    assert review["scientific_execution_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["reviewed_authority"]["sha256"] == _sha256(AUTHORITY_PATH)

