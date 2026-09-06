from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_v0 as packet,
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


def test_packet_consumes_exact_selection_and_stops_for_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["authority"]["selection_verdict"] == (
        "SELECTED_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_PREPARATION"
    )
    assert report["authority"]["terminal_prior_block"] == (
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
    )


def test_human_packet_is_bound_and_contains_required_boundaries() -> None:
    text = (REPO_ROOT / packet.PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "No current bound authority in this packet selects an at-most-second-order",
        "Showing that `F_EH` satisfies the requirements is not a uniqueness proof",
        "Exactly one result is permitted",
        "does not perform the analysis",
        "create an automation",
    ):
        assert token in text


def test_statement_provenance_classes_are_closed_and_second_order_is_supplied() -> None:
    contract = _report()["statement_provenance_contract"]
    assert contract["class_count"] == len(contract["classes"]) == 3
    assert contract["classes"] == packet.STATEMENT_CLASSES
    assert contract["exactly_one_initial_class_required"] is True
    assert contract["convenience_reclassification_allowed"] is False
    assert contract["second_order_field_equation_assumption"] == (
        "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION_ONLY"
    )


def test_requirement_inventory_is_complete_unique_and_unanalyzed() -> None:
    inventory = _report()["requirement_inventory"]
    assert inventory["requirement_count"] == len(inventory["rows"]) == 10
    assert inventory["constraint_class_count"] == len(packet.REQUIREMENT_CLASSES) == 9
    assert len({row["requirement_id"] for row in inventory["rows"]}) == 10
    assert all(row["source_bindings"] for row in inventory["rows"])
    assert all(row["selection_power_status"] == "NOT_ANALYZED" for row in inventory["rows"])
    assert inventory["analysis_executed"] is False
    assert inventory["numerical_requirement_weights_allowed"] is False


def test_recovery_obligations_are_not_misclassified_as_uniqueness_theorems() -> None:
    rows = {
        row["requirement_id"]: row
        for row in _report()["requirement_inventory"]["rows"]
    }
    assert "not an action uniqueness theorem" in rows["R8_NEWTON_POISSON"]["initial_boundary"]
    assert rows["R9_MOMENTUM_CURRENT"]["selection_power_status"] == "NOT_ANALYZED"
    assert rows["R10_STABILITY_NO_FIT"]["necessity"] == "REQUIRED_AFTER_CANDIDATE_EXISTS"


def test_comparison_family_envelope_is_finite_and_promotes_nothing() -> None:
    envelope = _report()["comparison_family_envelope"]
    assert envelope["family_count"] == len(envelope["rows"]) == 7
    assert envelope["finite_catalog"] is True
    assert envelope["catalog_exhaustive_over_all_gravity_theories"] is False
    assert envelope["family_adopted_or_activated_count"] == 0
    assert all(row["comparison_only"] is True for row in envelope["rows"])
    statuses = {row["envelope_status"] for row in envelope["rows"]}
    assert "PRIMARY_METRIC_LOCAL_ENVELOPE" in statuses
    assert "OUTSIDE_FROZEN_LOCAL_SCOPE" in statuses
    assert "EQUIVALENCE_CONTROL_NOT_SEPARATE_CANDIDATE" in statuses


def test_matrix_vocabulary_is_closed_and_no_matrix_was_computed() -> None:
    matrix = _report()["survival_elimination_matrix_contract"]
    assert matrix["row_count"] == 10
    assert matrix["column_count"] == 7
    assert matrix["cell_values"] == packet.MATRIX_CELL_VALUES
    assert matrix["elimination_requires_derivation_or_counterexample"] is True
    assert matrix["survival_means_adoption"] is False
    assert matrix["matrix_computed_by_preparation"] is False


def test_dependency_contract_blocks_duplicate_weight_and_preserves_00_0i_distinction() -> None:
    dependency = _report()["independence_redundancy_contract"]
    assert dependency["dependency_values"] == packet.DEPENDENCY_VALUES
    assert dependency["probe_count"] == len(dependency["probes"]) == 4
    assert dependency["duplicate_wording_adds_selection_power"] is False
    assert dependency["numerical_weighting_allowed"] is False
    probes = {row["probe_id"]: row for row in dependency["probes"]}
    assert probes["D_00_VERSUS_0I"]["members"] == [
        "R8_NEWTON_POISSON",
        "R9_MOMENTUM_CURRENT",
    ]


def test_standard_gr_is_an_isolated_oracle_not_a_selection_premise() -> None:
    isolation = _report()["standard_GR_isolation"]
    assert isolation["Einstein_Hilbert_role"] == "COMPARISON_ORACLE_ONLY"
    assert isolation["satisfaction_implies_uniqueness"] is False
    assert isolation["Einstein_equation_allowed_as_selection_premise"] is False
    assert isolation["comparator_activated"] is False


def test_equivalence_contract_is_local_bulk_and_preserves_physical_differences() -> None:
    equivalence = _report()["equivalence_contract"]
    assert equivalence["allowed_rule_count"] == len(equivalence["allowed_rules"]) == 5
    assert equivalence["forbidden_rule_count"] == len(equivalence["forbidden_equivalences"]) == 7
    assert equivalence["claim_scope"] == "LOCAL_BULK_ONLY"
    assert equivalence["global_boundary_quantum_equivalence_claimed"] is False
    assert "different propagating degrees of freedom" in equivalence["forbidden_equivalences"]


def test_distinctiveness_requires_demonstrated_selection_power() -> None:
    distinctiveness = _report()["distinctiveness_contract"]
    assert distinctiveness["test_count"] == len(distinctiveness["tests"]) == 7
    assert distinctiveness["at_least_one_demonstrated_test_required"] is True
    assert distinctiveness["repository_ownership_is_distinctiveness"] is False
    assert distinctiveness["methodological_rigor_alone_is_action_selection"] is False


def test_six_outcomes_have_exact_order_and_separate_underdetermination_from_postulate() -> None:
    outcomes = _report()["outcome_contract"]
    assert outcomes["outcome_count"] == len(outcomes["decision_order"]) == 6
    assert [row["order"] for row in outcomes["decision_order"]] == list(range(1, 7))
    assert [row["outcome"] for row in outcomes["decision_order"]] == [
        "REQUIREMENT_SET_INCONSISTENT",
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS",
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        "ACTION_FAMILY_UNDERDETERMINED",
        "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
    ]
    assert outcomes["postulate_required_requires_exhaustion_proof"] is True
    assert outcomes["inconsistency_and_no_go_are_distinct"] is True


def test_all_eight_controls_are_atomic_and_have_unique_diagnostics() -> None:
    controls = _report()["control_contract"]
    assert controls["control_count"] == len(controls["rows"]) == 8
    assert controls["all_single_mutation"] is True
    assert all(row["mutation_count"] == 1 for row in controls["rows"])
    assert len({row["first_diagnostic"] for row in controls["rows"]}) == 8
    assert controls["controls_executed_by_preparation"] is False
    assert controls["independent_review_execution_required"] is True


def test_packet_prepares_only_and_creates_no_theory_physics_tooling_or_automation() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_only"] is True
    for key, value in scope.items():
        if key != "packet_preparation_only":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No analysis",
        "principle",
        "postulate",
        "action",
        "matter sector",
        "variation",
        "tooling lane",
        "automation",
    ):
        assert token in claim
