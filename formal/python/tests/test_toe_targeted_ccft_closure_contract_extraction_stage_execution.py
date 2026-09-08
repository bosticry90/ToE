from __future__ import annotations

import hashlib

import pytest

from formal.python.tools import toe_targeted_ccft_closure_contract_extraction_stage_execution as execution


def test_frozen_checklists_have_exact_prepared_shape() -> None:
    assert len(execution.CHECKLISTS["CP_NLSE"]) == 10
    assert len(execution.CHECKLISTS["LCRD_V3"]) == 8
    assert sum(map(len, execution.CHECKLISTS.values())) == 18


def test_evidence_vocabulary_is_exactly_the_frozen_seven_classes() -> None:
    assert execution.EVIDENCE_CLASSES == {
        "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED",
        "PARTIAL_CONTRACT_RECOVERED",
        "CONFLICTING_SOURCE_CONTRACTS",
        "DERIVED_SUMMARY_WITH_PRIMARY_SOURCE_MISSING",
        "NUMERICAL_DEFAULT_ONLY",
        "HEURISTIC_NOT_A_CONTRACT",
        "NO_RELEVANT_EVIDENCE",
    }


def test_excerpt_selection_is_line_bounded_and_hashable() -> None:
    text = "alpha\ncontract anchor\nomega\n"
    start, end, excerpt = execution._extract_excerpt(
        text, {"anchor": "contract anchor", "before": 1, "after": 1}
    )
    assert (start, end, excerpt) == (1, 3, "alpha\ncontract anchor\nomega")
    assert hashlib.sha256(excerpt.encode("utf-8")).hexdigest()


def test_excerpt_selection_rejects_missing_anchor() -> None:
    with pytest.raises(ValueError, match="anchor not found"):
        execution._extract_excerpt("alpha\nbeta", {"anchor": "gamma"})


@pytest.mark.parametrize(
    ("classes", "expected"),
    [
        (["CONFLICTING_SOURCE_CONTRACTS"], "CONFLICTING_EVIDENCE_EXTRACTED"),
        (["EXACT_SOURCE_BOUND_CONTRACT_RECOVERED"], "EXACT_EVIDENCE_EXTRACTED_PENDING_STAGE_3_ADJUDICATION"),
        (["PARTIAL_CONTRACT_RECOVERED"], "ONLY_NONEXACT_EVIDENCE_EXTRACTED"),
        ([], "NO_RELEVANT_EVIDENCE_IN_SELECTED_SET"),
    ],
)
def test_checklist_status_preserves_adjudication_boundary(classes: list[str], expected: str) -> None:
    records = [{"evidence_strength_classification": item} for item in classes]
    assert execution._checklist_status(records) == expected


def test_execution_tool_has_no_archive_or_repository_traversal_api() -> None:
    source = execution.Path(execution.__file__).read_text(encoding="utf-8")
    assert ".rglob(" not in source
    assert "os.walk" not in source
    assert "subprocess" not in source
    assert "passive_text_capture" in source


def test_open_state_is_the_exact_stage_two_input_boundary() -> None:
    event = execution._load(execution.OPEN_EVENT)
    assert event["attempt_sequence_number"] == 2
    assert event["program_id"] == execution.PROGRAM_ID
    stage = execution._manifest_stage()
    assert stage["semantic_stage_id"] == execution.STAGE_ID
    assert stage["canonical_target"] == execution.TARGET


def test_stage_one_input_remains_fixed_and_balanced() -> None:
    by_path = execution._verify_frozen_inputs(execution._load(execution.STAGE1_RESULT))
    assert len(by_path) == 96
    assert sum(row["allocation_branch"] == "CP_NLSE" for row in by_path.values()) == 48
    assert sum(row["allocation_branch"] == "LCRD_V3" for row in by_path.values()) == 48
