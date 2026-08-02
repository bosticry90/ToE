from __future__ import annotations

import json

import pytest

from formal.python.tools import toe_targeted_ccft_contract_adjudication_stage_execution as execution


def _record(record_id: str = "X") -> dict:
    return {"contract_record_id": record_id}


def _decision(status: str, values: bool, reduction: str | None = None) -> dict:
    return {
        "record_id": "X",
        "adjudication_status": status,
        "criteria": {name: values for name in execution.CRITERIA},
        "future_postulate_reduction": reduction,
    }


def test_manifest_stage_three_target_and_scope_are_frozen() -> None:
    stage = execution._stage()
    assert stage["stage_number"] == 3
    assert stage["semantic_stage_id"] == execution.STAGE_ID
    assert stage["canonical_target"] == execution.TARGET
    assert stage["canonical_scope_hash"] == "5b6cf39bbf3e4f8bf076dba1817778547410a8d7950164ce5b1c27d0f977410a"


def test_recovered_candidate_requires_all_six_criteria_and_reduction() -> None:
    execution._validate_decision(
        _decision("RECOVERED_EXACT_CLOSURE_CONTRACT", True, "PERIODIC_DOMAIN"),
        _record(),
    )


def test_recovered_candidate_rejects_failed_criterion() -> None:
    decision = _decision("RECOVERED_EXACT_CLOSURE_CONTRACT", True, "X")
    decision["criteria"]["conflict_free"] = False
    with pytest.raises(ValueError, match="recovered status"):
        execution._validate_decision(decision, _record())


def test_nonrecovered_candidate_rejects_all_pass_criteria() -> None:
    with pytest.raises(ValueError, match="recovered status"):
        execution._validate_decision(
            _decision("EXACT_EVIDENCE_CONFIGURATION_BOUND_NOT_GENERAL_CONTRACT", True),
            _record(),
        )


def test_stage_two_input_contains_exactly_seven_exact_candidates() -> None:
    result = execution._load(execution.STAGE2_RESULT)
    exact = [
        row for row in result["source_bound_contract_record_ledger"]
        if row["evidence_strength_classification"] == "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED"
    ]
    assert len(result["source_bound_contract_record_ledger"]) == 23
    assert len(result["missing_contract_checklist_ledger"]) == 18
    assert len(exact) == 7


def test_execution_has_no_source_traversal_or_theorem_lane() -> None:
    text = execution.Path(execution.__file__).read_text(encoding="utf-8")
    assert ".rglob(" not in text
    assert "os.walk" not in text
    assert "subprocess" not in text
    assert "theorem_discovery_lane_opened" in text


def test_stage_three_open_event_is_attempt_three() -> None:
    event = json.loads(execution.OPEN_EVENT.read_text(encoding="utf-8"))
    assert event["attempt_sequence_number"] == 3
    assert event["program_id"] == execution.PROGRAM_ID
