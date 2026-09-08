from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_PREPARATION_AUTHORITY_v0.json"
)
REVIEW_PATH = (
    RELEASE
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_PREPARATION_AUTHORITY_REVIEW_v0.json"
)
TARGET = (
    "prepare_toe_native_gravitational_requirements_and_candidate_action_"
    "family_survey_bounded_program_v0"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_the_terminal_census_checkpoint() -> None:
    authority = _read(AUTHORITY_PATH)
    bound = authority["consumed_terminal_checkpoint"]
    for path_key, hash_key in (
        ("census_closeout_result_path", "census_closeout_result_sha256"),
        ("census_closeout_review_path", "census_closeout_review_sha256"),
    ):
        assert _sha256(REPO_ROOT / bound[path_key]) == bound[hash_key]
    assert bound["selected_frontier"] == (
        "HYP_TOE_NATIVE_GRAVITATIONAL_PRINCIPLE_ACTION_SELECTION_v0"
    )
    assert bound["selected_frontier_readiness"] == "AFTER_ONE_PREREQUISITE"


def test_authority_is_preparation_only() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["authority_decision"] == "AUTHORIZE_PROPOSAL_PREPARATION_ONLY"
    assert authority["authorized_target"] == TARGET
    assert authority["zero_scientific_execution"] is True
    prohibited = set(authority["prohibited_work"])
    assert "install the proposed program" in prohibited
    assert "open any scientific stage" in prohibited
    assert "select or endorse a gravitational action" in prohibited
    assert "populate or reuse the closed V2 automated scientific matrix" in prohibited


def test_independent_review_accepts_only_preparation_authority() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["decision"] == "ACCEPT_PROPOSAL_PREPARATION_AUTHORITY_ONLY"
    assert review["scientific_execution_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())

