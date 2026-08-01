from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
RESULT = RELEASE / "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_RESULT_v0.json"
REVIEW = RELEASE / "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_RESULT_REVIEW_v0.json"
AUTHORITY = RELEASE / "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_AUTHORITY_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
SELECTION_TARGET = "select_post_ccft_core_recovery_development_route_v0"
NEXT_TARGET = "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0"
CONSTRUCTION_TARGET = "prepare_bounded_ccft_v0_theory_construction_program"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_result_is_bound_to_separate_authority_commit() -> None:
    value = read(RESULT)
    assert value["execution_target"] == SELECTION_TARGET
    assert value["authority"]["sha256"] == sha(AUTHORITY)
    assert value["authority"]["authority_commit"] == "4a629d2f3d8b30a0a709635d2fb4a9f33c268327"


def test_targeted_recovery_is_the_only_immediate_selected_route() -> None:
    value = read(RESULT)
    assert value["terminal_outcome"] == "SELECT_ONE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY"
    assert value["selected_route"]["selected_preparation_target"] == NEXT_TARGET
    assert value["selected_route"]["preparation_authorized"] is False
    assert value["selected_route"]["archive_traversal_started"] is False
    assert len(value["decision_matrix"]) == 3


def test_search_has_one_pass_two_outcomes_and_no_retry() -> None:
    contract = read(RESULT)["targeted_recovery_contract"]
    assert contract["search_pass_limit"] == 1
    assert contract["general_census_prohibited"] is True
    assert contract["terminal_outcomes"] == [
        "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED",
        "NO_ADDITIONAL_CCFT_CLOSURE_EVIDENCE_FOUND",
    ]
    assert contract["automatic_second_search_authorized"] is False


def test_construction_handoff_is_binding_but_not_authorized() -> None:
    handoff = read(RESULT)["binding_post_recovery_handoff"]
    assert handoff["required_after_either_terminal_outcome"] is True
    assert handoff["target"] == CONSTRUCTION_TARGET
    assert handoff["preparation_authorized_now"] is False
    assert handoff["program_proposal_prepared"] is False
    assert handoff["program_installed"] is False
    assert handoff["program_opened"] is False
    assert handoff["separate_authority_required"] is True


def test_scientific_outputs_remain_absent() -> None:
    boundary = read(RESULT)["preserved_scientific_boundary"]
    assert boundary["closed_ccft_model_exists"] is False
    assert boundary["ccft_equation_repaired_or_selected"] is False
    assert boundary["new_ccft_postulate_inserted"] is False
    assert boundary["ccft_v0_constructed"] is False
    assert boundary["scientific_calculation_executed"] is False
    assert boundary["evidence_promoted"] is False


def test_review_and_registry_accept_nonexecuting_handoff() -> None:
    review = read(REVIEW)
    assert review["result_sha256"] == sha(RESULT)
    assert review["accepted"] is True
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    registry = read(REGISTRY)
    projection = registry["current_projection_v0"]
    assert projection["current_target"] == NEXT_TARGET
    assert projection["current_target_kind"] == "toe_targeted_ccft_closure_evidence_recovery_bounded_program_preparation_authorized_not_executed_v0"
    rows = [row for row in registry["workstreams"] if row.get("workstream_id") == NEXT_TARGET]
    assert len(rows) == 1
    assert rows[0]["status"] == "active"
