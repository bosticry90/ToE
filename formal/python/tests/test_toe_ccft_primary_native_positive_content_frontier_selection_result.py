from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
RESULT = RELEASE / "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_RESULT_v0.json"
REVIEW = RELEASE / "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_RESULT_REVIEW_v0.json"
AUTHORITY = RELEASE / "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_AUTHORITY_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
SELECTION_TARGET = "select_ccft_as_primary_native_positive_content_frontier_v0"
NEXT_TARGET = "prepare_toe_ccft_native_mathematical_core_and_operationalization_bounded_program_v0"


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_result_is_bound_to_the_separate_authority() -> None:
    value = _load(RESULT)
    assert value["execution_target"] == SELECTION_TARGET
    assert value["authority"]["sha256"] == _sha256(AUTHORITY)
    assert value["authority"]["authority_commit"] == (
        "193a01855148b5851a3a3324742d28f1669177a2"
    )


def test_ccft_is_selected_after_one_prerequisite_only() -> None:
    value = _load(RESULT)
    selected = value["selected_frontier"]
    assert value["terminal_outcome"] == (
        "CCFT_SELECTED_AS_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_AFTER_ONE_PREREQUISITE"
    )
    assert selected["readiness"] == "AFTER_ONE_PREREQUISITE"
    assert selected["selected_preparation_target"] == NEXT_TARGET
    assert selected["preparation_authorized"] is False
    assert selected["program_installed"] is False
    assert selected["scientific_stage_opened"] is False


def test_all_five_lanes_receive_distinct_roles() -> None:
    matrix = _load(RESULT)["decision_matrix"]
    assert len(matrix) == 5
    by_lane = {row["lane"]: row["classification"] for row in matrix}
    assert by_lane["CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION"] == (
        "PRIMARY_FRONTIER_AFTER_ONE_PREREQUISITE"
    )
    assert by_lane["GRAVITY_FIRST_NATIVE_DEVELOPMENT"] == (
        "BLOCKED_BY_ACCEPTED_NEGATIVE_RESULTS"
    )
    assert by_lane["MASTER_ACTION_FIRST_NATIVE_DEVELOPMENT"] == (
        "LATER_EMBEDDING_ROLE_ONLY"
    )


def test_prior_negative_results_and_nonexhaustion_are_preserved() -> None:
    limits = _load(RESULT)["preserved_scope_limitations"]
    assert limits["repository_claim_exhaustion_established"] is False
    assert limits["custody_records_outside_bounded_deep_review"] == 12923
    assert limits["earlier_coherence_operational_block_preserved"] is True
    assert limits["ccft_coherence_currently_coherent_candidates"] == 0
    assert limits["ccft_coherence_bounded_readiness"] == "BLOCKED_BY_MISSING_DEFINITION"
    assert limits["gravity_principle_terminal_block_preserved"] is True
    assert limits["native_gravity_action_selected"] is False


def test_selection_does_not_produce_scientific_model_outputs() -> None:
    value = _load(RESULT)
    assert all(item is None for item in value["scientific_outputs_produced"].values())
    boundary = value["successor_boundary"]
    assert boundary == {
        "preparation_target_selected": True,
        "preparation_execution_authorized": False,
        "program_proposal_prepared": False,
        "program_installed": False,
        "program_opened": False,
        "separate_authority_required": True,
    }


def test_independent_review_accepts_the_bounded_selection() -> None:
    review = _load(REVIEW)
    assert review["review_result"] == "PASS"
    assert all(review["checks"].values())
    assert review["independent_conclusion"] == (
        "CCFT_VALIDLY_SELECTED_AS_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_AFTER_ONE_PREREQUISITE_WITHOUT_SCIENTIFIC_ENDORSEMENT"
    )


def test_registry_retains_selection_and_preparation_workstreams() -> None:
    registry = _load(REGISTRY)
    selection_rows = [
        row for row in registry["workstreams"] if row.get("workstream_id") == SELECTION_TARGET
    ]
    next_rows = [
        row for row in registry["workstreams"] if row.get("workstream_id") == NEXT_TARGET
    ]
    assert len(selection_rows) == 1
    assert selection_rows[0]["status"] == "completed"
    assert len(next_rows) == 1
