from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
RESULT = RELEASE / "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
REVIEW = RELEASE / "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
PROGRAM_ID = "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0"


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_and_source_bindings_reproduce() -> None:
    value = _load(RESULT)
    authority = value["authority_binding"]
    assert _sha256(REPO_ROOT / authority["authority_path"]) == authority["authority_sha256"]
    assert _sha256(REPO_ROOT / authority["authority_review_path"]) == (
        authority["authority_review_sha256"]
    )
    for source in value["source_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_exact_five_stage_sequence_is_frozen() -> None:
    value = _load(RESULT)
    stages = value["stages"]
    assert [row["stage_number"] for row in stages] == [1, 2, 3, 4, 5]
    assert [row["semantic_stage_id"] for row in stages] == [
        "CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY",
        "CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION",
        "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION",
        "MINIMAL_CLOSED_CCFT_CORE_DECISION",
        "CCFT_VIABILITY_TEST_HANDOFF_DECISION",
    ]
    assert value["proposed_program_id"] == PROGRAM_ID
    assert value["mandatory_exit_target_proposed"] == (
        "close_toe_ccft_native_mathematical_core_and_operationalization_v0_after_bounded_result_v0"
    )


def test_program_is_bounded_and_has_no_repair_or_automatic_successor() -> None:
    controls = _load(RESULT)["program_controls"]
    assert controls["authorized_stage_count_proposed"] == 5
    assert controls["maximum_attempt_count_proposed"] == 5
    assert controls["repair_attempt_count"] == 0
    assert controls["no_subsidiary_scientific_targets"] is True
    assert controls["automatic_successor"] is False
    assert controls["maximum_source_artifacts_for_deep_review"] == 160
    assert controls["maximum_minimal_core_candidates"] == 12
    assert controls["maximum_total_extracted_text_bytes"] == 67108864


def test_content_classes_and_operational_questions_are_complete() -> None:
    value = _load(RESULT)
    assert value["mathematical_content_vocabulary"] == [
        "EXPLICIT_CCFT_MATHEMATICS",
        "PARTIAL_MATHEMATICAL_STRUCTURE",
        "HEURISTIC_OR_ANALOGY",
        "CONFLICTING_CCFT_FORMULATION",
        "UNDEFINED_SYMBOL_OR_TERM",
        "CONTROL_OR_KNOWN_PHYSICS_IMPORT",
    ]
    assert len(value["operationalization_questions"]) == 9
    assert "units_or_dimensional_status" in value["mathematical_object_record_fields"]
    assert "initial_or_boundary_data" in value["mathematical_object_record_fields"]


def test_terminal_outcomes_have_fixed_lifecycle_meanings() -> None:
    mapping = _load(RESULT)["program_terminal_outcome_lifecycle_mapping"]
    assert mapping == {
        "MINIMAL_SOURCE_BOUND_CCFT_CORE_READY_FOR_VIABILITY_TEST": "PASS",
        "CCFT_CORE_READY_ONLY_AS_BOUNDED_SURROGATE": "PASS",
        "CCFT_MATHEMATICS_RECOVERED_BUT_NOT_OPERATIONALIZABLE": "BLOCKED",
        "CCFT_FORMULATIONS_CONFLICT": "BLOCKED",
        "NO_CLOSED_CCFT_MATHEMATICAL_CORE_RECOVERED": "BLOCKED",
        "SOURCE_EVIDENCE_INSUFFICIENT": "BLOCKED",
        "DETERMINISTIC_ARTIFACT_GENERATION_FAILED": "FAILED",
    }


def test_proposal_claims_no_installation_or_ccft_physics() -> None:
    value = _load(RESULT)
    assert value["status"] == "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
    assert all(item is False for item in value["nonclaim_boundary"].values())
    assert value["source_scope_contract"]["repository_claim_exhaustion_may_be_claimed"] is False
    assert value["source_scope_contract"]["scientific_adoption_from_discovery"] is False


def test_independent_review_accepts_only_the_uninstalled_proposal() -> None:
    review = _load(REVIEW)
    assert review["accepted"] is True
    assert review["proposal_only"] is True
    assert review["program_installed"] is False
    assert review["scientific_stage_opened"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["reviewed_result"]["sha256"] == _sha256(RESULT)
