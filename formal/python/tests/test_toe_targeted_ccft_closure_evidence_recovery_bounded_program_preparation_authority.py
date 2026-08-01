from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_is_exactly_proposal_preparation() -> None:
    value = read(AUTHORITY)
    assert value["authority_decision"] == "AUTHORIZE_PROPOSAL_PREPARATION_ONLY"
    assert value["authorized_target"] == TARGET
    assert value["status"] == "PROGRAM_PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"
    assert value["zero_scientific_execution"] is True


def test_route_selection_bindings_and_hard_stop_reproduce() -> None:
    checkpoint = read(AUTHORITY)["consumed_route_selection"]
    assert sha(REPO_ROOT / checkpoint["selection_result_path"]) == checkpoint["selection_result_sha256"]
    assert sha(REPO_ROOT / checkpoint["selection_review_path"]) == checkpoint["selection_review_sha256"]
    assert checkpoint["selected_route"] == "SELECT_ONE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY"
    assert checkpoint["search_pass_limit"] == 1
    assert checkpoint["automatic_second_search_authorized"] is False


def test_authority_requires_exact_classifications_and_outcomes() -> None:
    value = read(AUTHORITY)
    assert len(value["required_evidence_classifications"]) == 7
    assert value["required_terminal_outcomes"] == [
        "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED",
        "NO_ADDITIONAL_CCFT_CLOSURE_EVIDENCE_FOUND",
    ]


def test_authority_prohibits_search_model_and_construction_execution() -> None:
    value = read(AUTHORITY)
    prohibited = set(value["prohibited_work"])
    assert "TRAVERSE_PARSE_SEARCH_OR_CLASSIFY_ARCHIVE_CONTENT" in prohibited
    assert "RUN_THE_TARGETED_RECOVERY_PASS" in prohibited
    assert "REPAIR_OR_HARMONIZE_A_CCFT_EQUATION" in prohibited
    assert "INSERT_A_NEW_CCFT_POSTULATE" in prohibited
    assert "PREPARE_INSTALL_OR_OPEN_THE_CCFT_V0_CONSTRUCTION_PROGRAM" in prohibited
    assert value["archive_traversal_authorized"] is False
    assert value["targeted_recovery_program_installed"] is False
    assert value["targeted_recovery_stage_opened"] is False
    assert value["ccft_v0_construction_preparation_authorized"] is False


def test_independent_review_accepts_only_preparation() -> None:
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert review["scientific_execution_authorized"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())


def test_registry_preserves_target_after_proposal_preparation_completes() -> None:
    registry = read(REGISTRY)
    projection = registry["current_projection_v0"]
    assert projection["current_target"] == TARGET
    assert projection["current_target_kind"] == "toe_targeted_ccft_closure_evidence_recovery_bounded_program_proposal_prepared_uninstalled_v0"
    assert projection["current_target_report"].endswith(
        "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
    )
    rows = [row for row in registry["workstreams"] if row.get("workstream_id") == TARGET]
    assert len(rows) == 1
    assert rows[0]["status"] == "active"
