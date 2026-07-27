from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_v1 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    assert packet.artifact_bytes() == packet.artifact_bytes() == REPORT_PATH.read_bytes()


def test_packet_preserves_every_frozen_authority_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    packet.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == packet.AUTHORITY_AND_SOURCE_HASHES


def test_packet_consumes_v0_block_and_stops_for_v1_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["authority"]["v0_review_verdict"] == (
        "BLOCKED_REQUIREMENTS_ACTION_SELECTION_CONTRACT_INCOMPLETE"
    )
    assert report["authority"]["retained_requirement_sources"] == 10
    assert report["authority"]["retained_comparison_families"] == 7


def test_all_ten_requirements_bind_exactly_one_source_compatible_class() -> None:
    contract = _report()["statement_class_contract"]
    assert contract["class_count"] == len(contract["classes"]) == 3
    assert contract["repaired_requirement_count"] == len(contract["rows"]) == 10
    assert contract["all_rows_bind_exactly_one_class"] is True
    assert contract["all_rows_source_class_compatible"] is True
    assert all(
        row["statement_class"] == "PROJECT_BOUND_NATIVE_REQUIREMENT"
        for row in contract["rows"]
    )
    assert all(
        row["statement_class"] == row["source_class_expected"]
        for row in contract["rows"]
    )
    assert len({row["canonical_requirement_id"] for row in contract["rows"]}) == 10


def test_supplied_assumptions_are_never_native_selection_inputs() -> None:
    contract = _report()["statement_class_contract"]
    assert contract["supplied_assumption_count"] == 3
    assert contract["supplied_assumptions_affect_native_elimination"] is False
    assert contract["supplied_assumptions_affect_native_distinctiveness"] is False
    assert all(
        row["statement_class"] == "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
        and row["native_elimination_allowed"] is False
        and row["native_distinctiveness_allowed"] is False
        for row in contract["supplied_assumptions"]
    )
    assert contract["active_new_postulate_count"] == 0


def test_matrix_has_seven_distinct_epistemic_states_and_real_cells_are_absent() -> None:
    matrix = _report()["matrix_contract"]
    assert matrix["cell_value_count"] == len(matrix["cell_values"]) == 7
    assert matrix["cell_values"] == packet.MATRIX_CELL_VALUES
    assert "NOT_DECIDABLE_FROM_REQUIREMENT" in matrix["cell_values"]
    assert matrix["undecidable_is_affirmative"] is False
    assert matrix["undecidable_is_elimination"] is False
    assert matrix["undecidable_is_not_evaluated"] is False
    assert matrix["real_matrix_cell_count"] == 70
    assert matrix["real_matrix_cells_supplied_by_preparation"] == 0


def test_preflight_rejects_missing_multiple_unknown_and_conflicting_classes() -> None:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    cases = []
    missing = packet._synthetic_requirement("R", include_statement_class=False)
    cases.append((missing, "MISSING_STATEMENT_CLASS"))
    multiple = packet._synthetic_requirement("R")
    multiple["statement_class"] = ["PROJECT_BOUND_NATIVE_REQUIREMENT"]
    cases.append((multiple, "MULTIPLE_STATEMENT_CLASSES"))
    unknown = packet._synthetic_requirement("R")
    unknown["statement_class"] = "UNKNOWN"
    unknown["source_class_expected"] = "UNKNOWN"
    cases.append((unknown, "UNKNOWN_STATEMENT_CLASS"))
    conflict = packet._synthetic_requirement("R")
    conflict["source_class_expected"] = "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    cases.append((conflict, "STATEMENT_CLASS_SOURCE_CONFLICT"))
    for requirement, diagnostic in cases:
        result = packet.evaluate_analysis(packet._fixture(
            [requirement], ["F_EH"], {"R": {"F_EH": affirmative}}
        ))
        assert result["diagnostic"] == diagnostic
        assert result["matrix_evaluated"] is False


def test_duplicate_canonical_requirement_fails_before_matrix() -> None:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    first = packet._synthetic_requirement("R_A", canonical_requirement_id="R")
    second = packet._synthetic_requirement("R_B", canonical_requirement_id="R")
    result = packet.evaluate_analysis(packet._fixture(
        [first, second],
        ["F_EH"],
        {"R_A": {"F_EH": affirmative}, "R_B": {"F_EH": affirmative}},
    ))
    assert result["diagnostic"] == "DUPLICATE_CANONICAL_REQUIREMENT"
    assert result["matrix_evaluated"] is False


def test_not_evaluated_blocks_scientific_outcome() -> None:
    requirement = packet._synthetic_requirement("R")
    result = packet.evaluate_analysis(packet._fixture(
        [requirement], ["F_EH"], {"R": {"F_EH": "NOT_EVALUATED"}}
    ))
    assert result["status"] == "ANALYSIS_INCOMPLETE"
    assert result["diagnostic"] == "NOT_EVALUATED_CELL_PRESENT"
    assert result["scientific_outcome"] is None


def test_supplied_elimination_is_traced_but_does_not_change_native_sets() -> None:
    controls = packet.run_production_controls()["controls"]
    row = next(
        item for item in controls
        if item["control_id"] == "CTRL_SUPPLIED_SECOND_ORDER_NOT_NATIVE"
    )
    assert row["passed"] is True
    assert row["observed"] == "ACTION_FAMILY_UNDERDETERMINED"


def test_undecidable_cell_is_unresolved_not_affirmative() -> None:
    controls = packet.run_production_controls()["controls"]
    row = next(
        item for item in controls if item["control_id"] == "CTRL_UNDECIDABLE_CELL"
    )
    assert row["passed"] is True
    assert row["observed"] == {
        "affirmative": ["F_EH"],
        "unresolved": ["F_FR"],
    }


def test_boundary_equivalence_reduces_to_one_local_bulk_class() -> None:
    controls = packet.run_production_controls()["controls"]
    row = next(
        item for item in controls
        if item["control_id"] == "CTRL_BOUNDARY_EQUIVALENCE"
    )
    assert row["passed"] is True
    assert row["observed"] == "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"


def test_unique_eh_and_unique_native_outcomes_are_disjoint() -> None:
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["controls"]
    }
    assert controls["CTRL_UNIQUE_NONDISTINCTIVE_EH"]["observed"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )
    assert controls["CTRL_UNIQUE_NATIVE_DISTINCTIVE"]["observed"] == (
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"
    )
    assert controls["CTRL_UNIQUE_NONDISTINCTIVE_EH"]["passed"] is True
    assert controls["CTRL_UNIQUE_NATIVE_DISTINCTIVE"]["passed"] is True


def test_underdetermination_and_postulate_required_boundary_is_executable() -> None:
    probes = packet.run_production_controls()["boundary_probes"]
    assert [row["observed"] for row in probes] == [
        "ACTION_FAMILY_UNDERDETERMINED",
        "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
    ]
    assert all(row["passed"] is True for row in probes)


def test_all_eight_controls_and_two_probes_share_one_production_path() -> None:
    execution = _report()["control_execution"]
    assert execution["control_count"] == execution["control_pass_count"] == 8
    assert execution["boundary_probe_count"] == execution["boundary_probe_pass_count"] == 2
    assert execution["all_used_shared_entry_point"] is True
    assert all(
        row["entry_point_id"] == packet.PRODUCTION_ENTRY_POINT_ID
        for row in execution["controls"] + execution["boundary_probes"]
    )
    assert all(row["passed"] is True for row in execution["controls"])


def test_real_scientific_analysis_and_downstream_physics_remain_unexecuted() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_only"] is True
    assert scope["synthetic_production_controls_executed"] is True
    for key, value in scope.items():
        if key not in {
            "packet_preparation_only",
            "synthetic_production_controls_executed",
        }:
            assert value is False, key
    retained = _report()["retained_boundaries"]
    assert retained["real_survivor_matrix"] == "NOT_COMPUTED"
    assert retained["native_gravitational_principle"] == "NOT_IDENTIFIED"
    assert retained["gravitational_action"] == "NOT_PROPOSED_OR_SELECTED"
    assert retained["standard_GR_comparator"] == "NOT_ACTIVATED"


def test_human_packet_records_shared_path_real_matrix_freeze_and_nonclaims() -> None:
    text = (REPO_ROOT / packet.PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "evaluate_analysis(analysis_input)",
        "NOT_DECIDABLE_FROM_REQUIREMENT",
        "These predicates are disjoint by construction",
        "All controls call `evaluate_analysis`",
        "real matrix cells supplied:",
        "create an automation",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
