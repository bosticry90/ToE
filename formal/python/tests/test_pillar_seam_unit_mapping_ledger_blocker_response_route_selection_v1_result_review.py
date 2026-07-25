from __future__ import annotations

import ast
from collections import Counter
from pathlib import Path
from typing import Any

import pytest

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1_result_review
    as subject,
)


EXPECTED_ROUTES = {
    "PILLAR-QFT-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-GR-units_and_dimensions-v0": "EQUATION_BALANCE_DERIVATION",
    "PILLAR-QM-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-STAT-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-EM-units_and_dimensions-v0": "CONVENTION_AND_CONSTANT_RESTORATION",
    "PILLAR-SR-units_and_dimensions-v0": "CONVENTION_AND_CONSTANT_RESTORATION",
    "PILLAR-COSMO-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "SEAM-QFT-GR-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-QM-STAT-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-EM-QFT-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-SR-COSMO-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-GR-QM-unit_map-v0": "RESEARCH_BLOCKED",
}

EXPECTED_ROUTE_COUNTS = {
    "EQUATION_BALANCE_DERIVATION": 1,
    "CONVENTION_AND_CONSTANT_RESTORATION": 2,
    "OBJECT_SEMANTICS_REFINEMENT": 4,
    "RESEARCH_BLOCKED": 5,
}

EXPECTED_NONCLAIMS = {
    "dimensional_closure",
    "pillar_completion",
    "seam_admissibility",
    "level_4_or_level_5",
    "physical_calibration_claims",
    "cross_sector_coupling_validation",
    "C_k_action_embedding",
    "CCFT_resumption",
    "master_action_promotion",
}

EXPECTED_CONTROL_IDS = {
    "assign_unit_to_unit_unknown_without_evidence",
    "natural_units_mark_unresolved_resolved",
    "dimensionless_coordinates_promoted_to_physical_distance",
    "suppressed_constant_omitted",
    "two_incompatible_routes_assigned_without_priority",
    "seam_map_selected_with_incomplete_pillar_units",
    "candidate_master_action_used_as_self_evidence",
    "normalization_convention_promoted_to_empirical_scale",
    "routed_blocker_promoted_to_dimensional_closure",
    "C_k_embedding_before_dimensions_known",
    "qft_action_claimed_without_action",
    "qm_hamiltonian_claimed_without_hamiltonian",
    "stat_probability_claimed_without_probability_semantics",
    "stat_transport_claimed_without_transport_law",
    "narrow_scalar_evidence_promoted_to_full_qft",
    "absence_treated_as_positive_evidence",
    "citation_hash_changed_without_rebinding",
    "route_rationale_object_missing_from_inventory",
    "speculative_surface_treated_as_authoritative",
    "one_source_supports_conflicting_object_definitions",
}


@pytest.fixture(scope="module")
def packet() -> dict[str, Any]:
    return subject.load_json(subject.PACKET_PATH)


@pytest.fixture(scope="module")
def ledger() -> dict[str, Any]:
    return subject.load_json(subject.LEDGER_PATH)


@pytest.fixture(scope="module")
def report() -> dict[str, Any]:
    # The subprocess reproduction is deliberately run once for the whole module.
    return subject.build_review_report(run_subprocesses=True)


def _rows(packet: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["row_id"]: row for row in packet["route_selections"]}


def _ledger_rows(ledger: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = [*ledger["pillar_rows"], *ledger["seam_rows"]]
    return {row["row_id"]: row for row in rows}


def test_exact_b_blocked_authority_class_ruling(report: dict[str, Any]) -> None:
    assert report["accepted"] is False
    assert report["verdict"] == "B-BLOCKED"
    assert report["primary_label"] == "B-BLOCKED"
    assert report["status"] == "blocked_source_authority_class_attribution_mismatch"
    assert report["review_outcome"] == subject.REVIEW_OUTCOME
    assert report["strict_review_outcome"] == subject.STRICT_REVIEW_OUTCOME
    assert report["mismatch_codes"] == subject.MISMATCH_CODES

    authority = report["source_authority_review"]
    assert authority["mismatch_count"] == 4
    assert authority["mismatch_codes"] == subject.MISMATCH_CODES
    assert authority["mismatch_checks"] == {
        code: True for code in subject.MISMATCH_CODES
    }
    assert authority["route_map_affected"] is False
    assert {
        item["source_id"] for item in authority["mismatches"]
    } == {
        "qft_bounded_surface",
        "qm_bounded_surface",
        "em_bounded_surface",
        "sr_bounded_surface",
    }
    for item in authority["mismatches"]:
        assert item["source_classification"] == "P-POLICY"
        assert item["packet_authority_class"] == "BOUNDED_AUTHORITATIVE_SURFACE"
        assert item["independently_derived_authority_class"] == (
            "BOUNDED_PLANNING_NONCLAIM"
        )


def test_twenty_five_of_twenty_six_decisions_reproduce(
    report: dict[str, Any],
) -> None:
    result = report["implemented_decision_reproduction"]
    failed = "supporting_sources_have_authorized_bounded_class"
    assert result["decision_count"] == 26
    assert result["passed_decision_count"] == 25
    assert result["failed_decision_ids"] == [failed]
    assert result["all_implemented_decisions_reproduced"] is False
    assert [item["decision_id"] for item in result["decisions"]] == (
        subject.DECISION_IDS
    )
    assert [
        item["decision_id"] for item in result["decisions"] if not item["passed"]
    ] == [failed]


def test_all_twenty_controls_reject_their_intended_mutations(
    report: dict[str, Any],
) -> None:
    result = report["negative_control_reproduction"]
    controls = result["controls"]
    assert result["control_count"] == 20
    assert result["all_controls_reproduced"] is True
    assert {item["control_id"] for item in controls} == EXPECTED_CONTROL_IDS
    assert all(item["fresh_deep_copy_used"] for item in controls)
    assert all(item["expected_failure_observed"] for item in controls)
    assert all(item["mutation_specific_delta_observed"] for item in controls)
    assert all(
        item["expected_failed_decision_id"] in item["observed_failed_decision_ids"]
        for item in controls
    )
    assert all(
        item["baseline_failed_decision_ids"]
        == ["supporting_sources_have_authorized_bounded_class"]
        for item in controls
    )
    baseline_overlap = {
        item["control_id"]
        for item in controls
        if item["baseline_already_failed_expected_decision"]
    }
    assert baseline_overlap == {"speculative_surface_treated_as_authoritative"}
    speculative = next(
        item
        for item in controls
        if item["control_id"] == "speculative_surface_treated_as_authoritative"
    )
    assert speculative["baseline_authority_mismatch_count"] == 4
    assert speculative["mutated_authority_mismatch_count"] == 5
    assert speculative["mutation_specific_delta_observed"] is True
    assert speculative["passed"] is True


def test_all_fourteen_requirements_are_recorded_with_only_requirement_three_blocked(
    report: dict[str, Any],
) -> None:
    review = report["formal_review_requirements"]
    requirements = review["requirements"]
    assert review["requirement_count"] == 14
    assert [item["requirement_id"] for item in requirements] == (
        subject.REVIEW_REQUIREMENT_IDS
    )
    assert review["failed_requirement_ids"] == ["formal_review_requirement_3"]
    assert review["all_requirements_passed"] is False
    assert requirements[2]["passed"] is False
    assert all(
        item["passed"]
        for index, item in enumerate(requirements)
        if index != 2
    )


def test_requirements_one_and_two_bind_exact_rows_and_frozen_inputs(
    packet: dict[str, Any], ledger: dict[str, Any], report: dict[str, Any]
) -> None:
    packet_rows = packet["route_selections"]
    ledger_rows = _ledger_rows(ledger)
    assert len(packet_rows) == 12
    assert len(_rows(packet)) == 12
    assert set(_rows(packet)) == set(ledger_rows)
    assert len(ledger_rows) == 12

    assert subject.sha256_path(subject.LEDGER_PATH) == (
        subject.EXPECTED_PREPARATION_HASHES[subject.LEDGER_REL]
    )
    assert subject.sha256_path(subject.LEDGER_REVIEW_PATH) == (
        subject.EXPECTED_PREPARATION_HASHES[subject.LEDGER_REVIEW_REL]
    )
    custody = report["artifact_chain"]["commit_custody"]
    assert custody["passed"] is True
    assert custody["preparation_commit"] == subject.PREPARATION_COMMIT
    assert custody["observed_parent"] == subject.PREPARATION_PARENT
    assert custody["parent_matches"] is True
    assert custody["all_artifacts_match"] is True
    assert custody["all_transitive_runtime_dependencies_bound_to_preparation_commit"] is True
    assert all(
        item["commit_blob_matches_expected"]
        and item["historical_blob_selected_for_validation"]
        and item["current_working_tree_equality_required"] is False
        for item in custody["artifacts"].values()
    )


def test_exact_source_absences_are_scoped_and_not_physical_no_go_claims(
    report: dict[str, Any],
) -> None:
    absence = report["source_absence_review"]
    assert absence["atomic_match_counts"] == {
        "qft_standalone_action_match_count": 0,
        "qm_hamiltonian_casefold_match_count": 0,
        "stat_probability_casefold_match_count": 0,
        "stat_transport_casefold_match_count": 0,
    }
    assert absence["all_atomic_absences_reproduced_from_source_bytes"] is True
    assert absence["packet_absence_checks_match_independent_rules"] is True
    assert absence["source_scope_absence_only"] is True
    assert absence["physical_nonexistence_or_no_go_claimed"] is False
    assert absence["source_hashes"] == {
        source_id: subject.SOURCE_BINDINGS[source_id]["sha256"]
        for source_id in (
            "qft_bounded_surface",
            "qm_bounded_surface",
            "stat_planning_surface",
        )
    }


def test_narrow_scalar_evidence_is_not_promoted_to_full_qft(
    packet: dict[str, Any], report: dict[str, Any]
) -> None:
    qft = _rows(packet)["PILLAR-QFT-units_and_dimensions-v0"]
    matrix = qft["evidence_matrix"]
    assert matrix["scalar_evidence_scope"] == "NARROW_CLASSICAL_REAL_SCALAR_ONLY"
    assert qft["selected_response_route"] == "OBJECT_SEMANTICS_REFINEMENT"
    assert "qft_scalar_sandbox_explicit" in qft["route_support_proposition_ids"]
    assert "qft_direct_physical_action_absent" not in (
        qft["route_support_proposition_ids"]
    )
    decision = next(
        item
        for item in report["implemented_decision_reproduction"]["decisions"]
        if item["decision_id"] == "narrow_scalar_evidence_is_not_promoted_to_full_qft"
    )
    assert decision["passed"] is True


def test_each_seam_is_blocked_by_its_actual_endpoint_states(
    packet: dict[str, Any], ledger: dict[str, Any]
) -> None:
    packet_rows = _rows(packet)
    pillar_states = {
        row["pillar_id"]: row["guardrail_unit_state"]
        for row in ledger["pillar_rows"]
    }
    for seam in ledger["seam_rows"]:
        row = packet_rows[seam["row_id"]]
        assert row["selected_response_route"] == "RESEARCH_BLOCKED"
        exact_states = {
            pillar_id: pillar_states[pillar_id]
            for pillar_id in seam["pillar_ids"]
        }
        assert all(state in {"unit_unknown", "unresolved"} for state in exact_states.values())
        proposition = next(
            item
            for item in row["evidence_matrix"]["propositions"]
            if item["proposition_id"].endswith("_route_research_blocked")
        )
        assert proposition["derived_facts"]["endpoint_states"] == exact_states
        assert proposition["derivation_rule"] == (
            "UNRESOLVED_ENDPOINTS_BLOCK_SEAM_CONVERSION"
        )


def test_every_rationale_object_has_supported_evidence(
    packet: dict[str, Any],
) -> None:
    for row in packet["route_selections"]:
        matrix = row["evidence_matrix"]
        supported_ids = set(matrix["supported_proposition_ids"])
        supported_objects = {
            obj["object_id"]
            for proposition in matrix["propositions"]
            if proposition["proposition_id"] in supported_ids
            and proposition["supports_route"] is True
            for obj in proposition["objects"]
        }
        assert set(matrix["rationale_object_ids"]) <= supported_objects


def test_route_map_and_one_two_four_five_distribution_are_reproduced(
    packet: dict[str, Any], report: dict[str, Any]
) -> None:
    route_review = report["route_reproduction"]
    assert route_review["independently_recomputed_routes"] == EXPECTED_ROUTES
    assert route_review["independently_recomputed_route_counts"] == (
        EXPECTED_ROUTE_COUNTS
    )
    assert Counter(
        row["selected_response_route"] for row in packet["route_selections"]
    ) == Counter(EXPECTED_ROUTE_COUNTS)
    assert route_review["route_map_reproduced"] is True
    assert route_review["route_map_accepted"] is False
    assert route_review["rows_remaining_blocked"] == 12
    assert route_review["resolved_row_count"] == 0


def test_no_dimensional_content_or_resolution_is_introduced(
    packet: dict[str, Any], report: dict[str, Any]
) -> None:
    assert subject._contains_assignment_key(packet) is False
    assert Counter(
        row["current_status"] for row in packet["route_selections"]
    ) == Counter({"unit_unknown": 6, "unresolved": 6})
    assert all(
        row["current_status"] != "resolved"
        for row in packet["route_selections"]
    )
    boundary = report["boundary"]
    assert boundary["unit_or_dimension_assignment_emitted"] is False
    assert boundary["normalization_or_constant_restoration_emitted"] is False
    assert boundary["route_map_changed_by_review"] is False


def test_all_nonclaims_and_maintenance_boundaries_remain_intact(
    packet: dict[str, Any], report: dict[str, Any]
) -> None:
    assert set(packet["nonclaims"]) == EXPECTED_NONCLAIMS
    for key, value in report["boundary"].items():
        if key != "route_map_changed_by_review":
            assert value is False, key
    assert report["maintenance_boundary"] == {
        "registry_maintenance_paused": True,
        "registry_monolith_remains_authoritative": True,
        "registry_v3_live": False,
        "stage_a_authorized": False,
        "stage_b_authorized": False,
    }


def test_isolated_regeneration_is_byte_identical_and_nonmutating(
    report: dict[str, Any],
) -> None:
    regeneration = report["regeneration"]
    assert regeneration["isolated_subprocess_count"] == 2
    assert regeneration["return_codes"] == [0, 0]
    assert regeneration["distinct_temporary_roots_used"] is True
    assert regeneration["all_frozen_inputs_staged_from_exact_hash_verified_bytes"] is True
    assert regeneration[
        "transitive_v0_generator_and_repo_environment_commit_custody_verified"
    ] is True
    assert regeneration["run_outputs_byte_identical"] is True
    assert regeneration["committed_packet_manifest_and_report_bytes_reproduced"] is True
    assert regeneration["repository_preparation_artifact_hashes_unchanged"] is True
    assert regeneration["run_artifact_hashes"][0] == (
        regeneration["run_artifact_hashes"][1]
    )
    assert regeneration["passed"] is True


def test_only_versioned_v2_correction_is_authorized(
    report: dict[str, Any],
) -> None:
    assert report["selected_next_target"] == subject.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == subject.SELECTED_NEXT_TARGET_KIND
    assert report["diagnostic_target"] == subject.DIAGNOSTIC_TARGET
    assert report["successor_boundary"] == {
        "corrective_successor": subject.SELECTED_NEXT_TARGET,
        "deferred_first_resolution_guardrail_after_future_acceptance": (
            subject.DEFERRED_FIRST_RESOLUTION_GUARDRAIL
        ),
        "first_resolution_guardrail_selected_now": False,
        "metadata_only_correction_required": True,
    }
    assert report["authority_rotation"] == {
        "packet_acceptance_authorized": False,
        "corrective_v2_preparation_authorized": True,
        "first_blocker_resolution_guardrail_authorized": False,
        "actual_blocker_resolution_execution_authorized": False,
        "sr_convention_or_restoration_work_authorized": False,
        "gr_equation_balance_derivation_authorized": False,
        "maintenance_authority_rotation_authorized": False,
    }
    assert report["failure_preservation"] == {
        "preparation_commit_remains_immutable": True,
        "preparation_artifacts_amended_by_review": False,
        "versioned_successor_required": True,
        "route_map_preserved_as_nonaccepted_evidence": True,
    }


def test_reviewer_does_not_import_v1_preparation_helpers(
    report: dict[str, Any],
) -> None:
    source = Path(subject.SCRIPT_PATH).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imports.append(node.module or "")
    assert all(
        "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1"
        not in module
        for module in imports
    )
    assert report["review_implementation"][
        "imports_v1_preparation_validator_or_controls"
    ] is False
    assert "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1" not in (
        subject.independent_decision_failures.__code__.co_names
    )
    assert "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1" not in (
        subject.independent_negative_controls.__code__.co_names
    )
