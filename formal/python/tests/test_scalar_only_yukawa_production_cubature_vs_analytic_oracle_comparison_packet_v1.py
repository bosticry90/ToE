from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1
    as packet,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_freezes_selector_and_v0() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_selector_artifacts"]
    } == packet.SELECTOR_HASHES
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_v0_packet_artifacts"]
    } == packet.V0_PACKET_HASHES


def test_only_seven_failed_gates_are_repaired() -> None:
    repair = _report()["v1_repair_scope"]
    assert repair["repaired_review_gate_count"] == 7
    assert repair["repaired_review_gates"] == list(packet.REPAIRED_REVIEW_GATES)
    assert repair["all_other_review_gates"] == "FROZEN"
    assert repair["automatic_v2"] == "PROHIBITED"
    assert _report()["frozen_v0_surfaces"]["accepted_review_gate_count"] == 33


def test_exact_96_cell_source_map_separates_three_evidence_scopes() -> None:
    source = _report()["production_source_and_attribution_contract"]
    rows = source["source_rows"]
    assert len(rows) == 96
    assert source["source_counts"] == {
        "HISTORICAL_STAGE_A_YUKAWA": 18,
        "MIRROR_NEWTONIAN_COMPANION": 48,
        "PARAMETERIZED_MIRROR_YUKAWA_EXTENSION": 30,
    }
    assert source["historical_decision_bearing_case_ids"] == list(packet.LEGACY_CASE_IDS)
    assert source["historical_decision_bearing_component"] == "YUKAWA_ONLY"
    assert source["historical_function_called_directly"] is True
    assert source["newtonian_historical_claim"].startswith("FORBIDDEN")
    assert source["unequal_radius_historical_claim"] == "FORBIDDEN"


def test_historical_equivalence_rule_is_fully_executable() -> None:
    rule = _report()["historical_path_equivalence_contract"]
    assert rule["control_id"] == "C00_HISTORICAL_MIRROR_EQUIVALENCE"
    assert rule["case_ids"] == list(packet.LEGACY_CASE_IDS)
    assert rule["orders"] == [8, 16, 24]
    assert rule["components"] == ["YUKAWA"]
    assert rule["absolute_tolerance_J"] == 1e-36
    assert rule["relative_tolerance"] == 5e-14
    assert "HISTORICAL_FIRST_THEN_MIRROR_ORDINARY" in rule["execution_order"]
    assert rule["failure_consequence"].startswith("BLOCKED_PRODUCTION_PATH_IDENTITY")


def test_slow_fit_and_economic_rule_are_numeric() -> None:
    slow = _report()["classification_contract_v1"]["slow_convergence_fit"]
    assert slow["full_fit_orders"] == [16, 24, 32, 40, 48]
    assert slow["tail_fit_orders"] == [24, 32, 40, 48]
    assert slow["minimum_r_squared_each_fit"] == 0.98
    assert slow["maximum_relative_exponent_difference"] == 0.20
    assert slow["minimum_required_order_for_label"] == 49
    assert slow["maximum_admissible_extrapolated_order"] == 192
    assert slow["runtime_fit_minimum_r_squared"] == 0.95
    assert "GT_60" in slow["economic_inferiority_rule"]
    assert "GT_1200" in slow["economic_inferiority_rule"]


def test_systematic_bias_is_component_separated() -> None:
    bias = _report()["classification_contract_v1"]["systematic_bias"]
    assert bias["grouping"].startswith("SEPARATELY_PER_COMPONENT")
    assert bias["orders"] == [32, 40, 48]
    assert bias["minimum_qualifying_cases_per_component"] == 4
    assert bias["maximum_relative_spread"] == 0.005
    assert bias["minimum_absolute_median_bias"] == 0.001
    assert bias["same_sign_required"] is True
    assert bias["label"] == "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED"


def test_yukawa_fingerprint_vector_metric_and_thresholds_are_exact() -> None:
    fingerprint = _report()["classification_contract_v1"]["yukawa_mutation_fingerprint"]
    assert fingerprint["reference_control"] == "C02_MISSING_A_Y_ONE_THIRD"
    assert fingerprint["case_order"] == list(packet.CASE_IDS)
    assert fingerprint["order_within_case"] == [32, 40, 48]
    assert fingerprint["vector_length"] == 24
    assert fingerprint["maximum_relative_l2_distance"] == 0.05
    assert fingerprint["maximum_entrywise_absolute_difference"] == 0.10
    assert fingerprint["minimum_nonzero_sign_agreement_count"] == 23
    assert fingerprint["required_sign_comparison_count"] == 24


def test_all_eleven_controls_have_complete_routes() -> None:
    controls = _report()["mandatory_control_contract"]
    assert controls["path_identity_preflight_count"] == 1
    assert controls["frozen_mutation_control_count"] == 10
    assert controls["total_mandatory_control_count"] == 11
    rows = controls["rows"]
    assert [row["control_id"] for row in rows[1:]] == [
        "C01_POINT_EQUIVALENT_NEWTONIAN",
        "C02_MISSING_A_Y_ONE_THIRD",
        "C03_GAP_FOR_CENTER_DISTANCE",
        "C04_RADIUS_AS_DIAMETER",
        "C05_ONE_DIMENSION_UNREFINED",
        "C06_WEIGHT_NORMALIZATION_BIAS",
        "C07_COMPONENT_CHANNEL_SWAP",
        "C08_ORDER_METADATA_OVERCLAIM",
        "C09_ORACLE_OVERWRITE",
        "C10_CONSTANT_MULTIPLICATIVE_BIAS",
    ]
    for row in rows:
        assert row["case_ids"]
        assert row["orders"]
        assert row["components"]
        assert row["execution_order"]
        assert row["injection_point"]
        assert row["acceptance_rule"]
        assert row["failure_consequence"]


def test_completion_precedence_suppresses_all_partial_classification() -> None:
    completion = _report()["completion_and_precedence_contract"]
    assert completion["required_unique_scientific_cells"] == 96
    assert completion["required_mandatory_controls"] == 11
    assert completion["partial_atomic_cells"].startswith("CUSTODY_EVIDENCE_ONLY")
    assert completion["scientific_labels_on_priority_1_2_or_3"] == (
        "FORBIDDEN_EMPTY_LIST_REQUIRED"
    )
    assert completion["completed_subset_classification"] == "FORBIDDEN"
    assert [row["priority"] for row in completion["exclusive_precedence"]] == [1, 2, 3, 4]
    assert completion["exclusive_precedence"][-1]["exclusive_outcome"] == (
        "EVALUATE_EXACT_NINE_SCIENTIFIC_LABELS"
    )


def test_nine_scientific_labels_and_review_outcomes_are_exact() -> None:
    contract = _report()["classification_contract_v1"]
    assert contract["scientific_labels_exact"] == list(packet.SCIENTIFIC_LABELS)
    assert _report()["packet_review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)
    assert contract["post_result_change"] == "FORBIDDEN"
    assert contract["favorable_rounding"] == "FORBIDDEN"


def test_packet_gates_and_scope_authorize_review_only() -> None:
    report = _report()
    gates = report["packet_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 46
    assert gates["failure_count"] == 0
    scope = report["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "v1_packet_prepared",
        "selector_authority_verified",
        "v0_packet_hash_frozen",
        "thirty_three_accepted_review_gates_frozen",
        "seven_failed_review_gates_repaired_in_contract",
        "independent_v1_packet_review_authorized",
    }
    assert scope["comparison_execution_authorized"] is False
    assert scope["scientific_comparison_cells_computed"] is False
    assert scope["automatic_v2_authorized"] is False


def test_human_packet_records_exact_boundary_and_next_authority() -> None:
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "18 historical Stage A Yukawa cells",
        "48 Newtonian companion cells",
        "30 mirror-extension Yukawa cells",
        "all 96 scientific cells",
        "all eleven mandatory controls",
        "No automatic V2",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
