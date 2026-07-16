from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_r13_numerical_block_route_selection_packet_v0
    as selection,
)


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict]:
    return selection.build_artifacts()


@pytest.fixture(scope="module")
def packet(artifacts: tuple[dict, dict, dict]) -> dict:
    return artifacts[0]


def test_generated_route_selection_artifacts_are_current(
    artifacts: tuple[dict, dict, dict],
) -> None:
    packet, manifest, report = artifacts
    assert selection.PACKET_PATH.read_bytes() == selection.canonical_json_bytes(packet)
    assert selection.MANIFEST_PATH.read_bytes() == selection.canonical_json_bytes(manifest)
    assert selection.REPORT_PATH.read_bytes() == selection.canonical_json_bytes(report)


def test_accepted_diagnostic_review_and_all_203_outputs_have_exact_custody(
    packet: dict,
) -> None:
    custody = packet["source_custody"]
    assert custody["passed"] is True
    assert custody["all_source_artifact_hashes_exact"] is True
    assert custody["source_artifact_hashes"] == selection.EXPECTED_SOURCE_HASHES
    assert custody["accepted_diagnostic_review_authority_exact"] is True
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["canonical_root_file_count"] == 205
    assert custody["canonical_root_digest"] == selection.EXPECTED_CANONICAL_ROOT_DIGEST
    assert custody["execution_count_performed"] == 1


def test_packet_preparation_is_read_only_and_does_not_import_simulator(packet: dict) -> None:
    before = selection.canonical_root_digest()
    selection.build_artifacts()
    after = selection.canonical_root_digest()
    source = (selection.REPO_ROOT / selection.GENERATOR_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    assert before == after == selection.EXPECTED_CANONICAL_ROOT_DIGEST
    assert " as simulator" not in source
    assert packet["source_custody"]["new_simulation_run_count"] == 0
    assert packet["source_custody"]["canonical_output_mutation_count"] == 0


def test_three_unresolved_mechanism_questions_are_preserved(packet: dict) -> None:
    questions = packet["unresolved_mechanism_questions"]
    assert len(questions) == 3
    assert {item["mechanism_id"] for item in questions} == selection.MECHANISM_IDS
    assert all(item["minimum_required_observables"] for item in questions)
    assert packet["inherited_authority"]["root_numerical_mechanism_status"] == "UNRESOLVED"


def test_six_routes_are_ranked_in_the_declared_order(packet: dict) -> None:
    routes = packet["route_catalog"]
    assert len(routes) == 6
    assert [item["rank"] for item in routes] == [1, 2, 3, 4, 5, 6]
    assert packet["selection_framework"]["ranking"] == [item["route_id"] for item in routes]
    assert packet["selection_framework"]["weighted_physical_score_used"] is False
    assert packet["selection_framework"]["post_hoc_threshold_or_fit_optimization_used"] is False


def test_route_A_uniquely_covers_all_three_mechanism_questions_without_method_change(
    packet: dict,
) -> None:
    routes = {item["route_id"]: item for item in packet["route_catalog"]}
    route_a = routes["ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"]
    assert route_a["rank"] == 1
    assert set(route_a["direct_mechanism_coverage"]) == selection.MECHANISM_IDS
    assert route_a["direct_mechanism_coverage_count"] == 3
    assert route_a["new_diagnostic_instrumentation_required"] is True
    assert route_a["new_numerical_method_introduced"] is False
    assert route_a["new_physical_model_introduced"] is False
    assert all(
        item["direct_mechanism_coverage_count"] == 0
        for route_id, item in routes.items()
        if route_id != route_a["route_id"]
    )


def test_tolerance_and_duration_routes_are_supporting_modules_only(packet: dict) -> None:
    routes = {item["route_id"]: item for item in packet["route_catalog"]}
    route_b = routes["ROUTE_B_EXPANDED_TOLERANCE_LADDER"]
    route_c = routes["ROUTE_C_DURATION_SCALING_EXPERIMENT"]
    assert route_b["route_class"] == "SUPPORTING_SCALING_MODULE"
    assert route_c["route_class"] == "SUPPORTING_TIME_GROWTH_MODULE"
    assert route_b["disposition"] == "SUPPORTING_COMPONENT_CANDIDATE_FOR_ROUTE_A_DESIGN"
    assert route_c["disposition"] == "SUPPORTING_COMPONENT_CANDIDATE_FOR_ROUTE_A_DESIGN"


def test_method_precision_and_domain_routes_have_explicit_deferrals(packet: dict) -> None:
    routes = {item["route_id"]: item for item in packet["route_catalog"]}
    route_d = routes["ROUTE_D_CONSTRAINT_PRESERVING_METHOD_COMPARISON"]
    route_e = routes["ROUTE_E_HIGHER_PRECISION_ARITHMETIC"]
    route_f = routes["ROUTE_F_CERTIFIED_NUMERICAL_DOMAIN_DECLARATION"]
    assert route_d["new_numerical_method_introduced"] is True
    assert route_d["disposition"] == "DEFER_UNTIL_CURRENT_METHOD_MECHANISM_IS_INSTRUMENTED"
    assert route_e["disposition"] == "DEFER_PENDING_CANCELLATION_CONDITIONING_EVIDENCE"
    assert route_f["new_run_required_if_later_authorized"] is False
    assert route_f["route_class"] == "NO_NEW_DATA_ENGINEERING_FALLBACK"


def test_selected_future_design_obligations_cover_exchange_blocks_and_closure(
    packet: dict,
) -> None:
    selected = packet["provisional_selection"]
    observables = " ".join(selected["mandatory_mechanism_observables_for_future_design_packet"])
    assert selected["route_id"] == "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"
    assert "field-sector exchange" in observables
    assert "matter-sector exchange" in observables
    assert "residual vectors" in observables
    assert "discrete divergence" in observables
    assert "closure audit residual" in observables
    assert selected["experiment_design_authorized_now"] is False
    assert selected["experiment_execution_authorized_now"] is False


def test_tolerances_durations_and_neighbor_are_candidates_not_frozen_roles(packet: dict) -> None:
    selected = packet["provisional_selection"]
    modules = selected["supporting_modules_to_evaluate_not_assume"]
    assert modules == [
        "the three original tolerance roles",
        "one or two intermediate tolerance roles",
        "multiple frozen duration checkpoints",
        "a matched passing-neighbor contrast",
    ]
    assert packet["authority_boundary"]["experiment_frozen"] is False
    assert "no run matrix frozen" in packet["nonclaims"]


def test_packet_preserves_canonical_block_materiality_and_claim_ceiling(packet: dict) -> None:
    inherited = packet["inherited_authority"]
    assert inherited["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
    assert inherited["blocked_row"] == "R13_CORNER_STRONG_LOW"
    assert inherited["blocked_role"] == "SOLVER_TOL1eM08"
    assert inherited["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert inherited["new_E_REPRO"] == "NONE"
    assert packet["decision_vs_mechanism_observables"][
        "future_design_must_freeze_both_classes"
    ]


def test_packet_passes_all_decisions_and_rotates_only_to_independent_review(
    packet: dict,
) -> None:
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["passed_decision_count"] == packet["decision_count"] == 20
    assert packet["failed_decision_ids"] == []
    assert packet["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert packet["downstream_target_if_independent_review_accepts"] == (
        selection.DOWNSTREAM_TARGET_IF_ACCEPTED
    )
    boundary = packet["authority_boundary"]
    assert boundary["route_selection_packet_prepared"] is True
    assert boundary["route_selection_independently_accepted"] is False
    assert boundary["experiment_design_packet_authorized"] is False
    assert boundary["new_simulation_authorized"] is False
    assert boundary["rerun_authorized"] is False
    assert boundary["threshold_or_fit_change_authorized"] is False
    assert boundary["robustness_reclassification_authorized"] is False
    assert boundary["materiality_classification_authorized"] is False
    assert boundary["new_E_REPRO_authorized"] is False
