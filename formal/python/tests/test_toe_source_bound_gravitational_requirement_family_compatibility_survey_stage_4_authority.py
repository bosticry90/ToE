from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = RELEASE_ROOT / (
    "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_"
    "SURVEY_STAGE_4_OPEN_AUTHORITY_v0.json"
)
REVIEW_PATH = RELEASE_ROOT / (
    "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_"
    "SURVEY_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_four_scope_and_matrix() -> None:
    authority = _read(AUTHORITY_PATH)
    stage = authority["authorized_stage"]
    assert authority["program_id"] == (
        "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_"
        "SURVEY_V0"
    )
    assert stage == {
        "stage_number": 4,
        "semantic_stage_id": "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY",
        "canonical_target": (
            "survey_toe_source_bound_gravitational_requirement_family_"
            "compatibility_v0"
        ),
        "canonical_scope_hash": (
            "e81613ed69adbe5c5586a2b9fcb22217f721923758f7af0d85a71cce84a51c51"
        ),
    }
    assert len(authority["requirement_ids"]) == 10
    assert len(set(authority["requirement_ids"])) == 10
    assert len(authority["family_ids"]) == 7
    assert len(set(authority["family_ids"])) == 7
    assert authority["compatibility_cell_count"] == 70


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY_PATH)
    for binding in authority["evidence_bindings"]:
        assert _sha256(REPO_ROOT / binding["path"]) == binding["sha256"]


def test_authority_freezes_role_aware_closed_cell_vocabulary() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["compatibility_state_vocabulary"] == [
        "SATISFIED_BY_SOURCE_BOUND_EVIDENCE",
        "VIOLATED_BY_SOURCE_BOUND_EVIDENCE",
        "PARTIALLY_SATISFIED",
        "NOT_TESTABLE_MISSING_DEFINITION",
        "NOT_TESTABLE_MISSING_DOWNSTREAM_INPUT",
        "NOT_APPLICABLE_NOT_AN_ACTION",
        "OUTSIDE_NATIVE_ROLE",
        "BLOCKED_BY_ACCEPTED_NEGATIVE_RESULT",
    ]
    contract = authority["cell_contract"]
    assert all(contract.values())
    roles = authority["family_role_contract"]
    assert roles["F_EH"] == "DEFINED_KNOWN_PHYSICS_BASELINE_NOT_NATIVE_DERIVED"
    assert roles["F_QUADRATIC"] == "DEFINED_REFERENCE_CONTROL_ONLY"
    assert roles["F_EQUIVALENCE_PROBE"] == "NONACTION_DIAGNOSTIC_CONTROL"
    assert roles["F_EXTRA_FIELD"] == "VERBAL_DIRECTION_ONLY"
    assert roles["F_NONLOCAL"] == "VERBAL_DIRECTION_ONLY"
    assert roles["F_CONNECTION_TORSION"] == "VERBAL_DIRECTION_ONLY"


def test_authority_prohibits_action_selection_invention_and_stage_five() -> None:
    authority = _read(AUTHORITY_PATH)
    prohibited = " ".join(authority["prohibited_work"])
    for phrase in (
        "invent an action",
        "treat all seven family labels as testable actions",
        "promote Einstein-Hilbert",
        "promote quadratic gravity",
        "reopen or extend quadratic-gravity calculations",
        "select the final gravitational action",
        "open Stage 5 automatically",
    ):
        assert phrase in prohibited
    assert authority["likely_conclusion_is_not_prejudged_result"] is True


def test_independent_review_accepts_authority_without_scientific_result() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    output = review["scientific_output_at_authority_checkpoint"]
    assert output == {
        "compatibility_cells_populated": 0,
        "families_eligible_for_native_selection": 0,
        "gravitational_actions_selected": 0,
        "new_gravitational_calculations": 0,
        "evidence_promoted": False,
    }
    assert review["stage_5_authorized"] is False
