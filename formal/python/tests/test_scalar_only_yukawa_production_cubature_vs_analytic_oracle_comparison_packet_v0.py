from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0
    as packet,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_packet_regenerates_and_consumes_exact_selector_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["status"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_selector_artifacts"]
    } == packet.SELECTOR_HASHES


def test_all_scientific_paths_are_hash_pinned() -> None:
    observed = {
        row["relative_path"]: row["sha256"]
        for row in _report()["authority"]["frozen_scientific_paths"]
    }
    assert observed == packet.SCIENTIFIC_PATH_HASHES
    for relative_path, expected in packet.SCIENTIFIC_PATH_HASHES.items():
        assert _sha256(ROOT / relative_path) == expected


def test_production_and_oracle_path_identity_is_explicit() -> None:
    report = _report()
    production = report["production_path_identity"]
    assert production["stage_a_yukawa_function"] == (
        "reduced_four_dimensional_density_integral_yukawa_energy"
    )
    assert production["parameterized_mirror_function"] == "_fixed_density_integral"
    assert production["dimensions_refined_together"] == ["r1", "mu1", "r2", "mu2"]
    assert production["legacy_equivalence_control_required"] is True
    assert "NOT_A_SEPARATE_STAGE_A_SCIENTIFIC_OUTPUT" in production[
        "newtonian_channel_qualification"
    ]
    assert production["production_repair_or_algorithm_change"] == "FORBIDDEN"
    oracle = report["oracle_path_identity"]
    assert oracle["energy_function"] == "_uy_stable_float"
    assert oracle["radial_function"] == "_radial_h"
    assert oracle["oracle_values_read_only"] is True


def test_eight_frozen_cases_cover_failures_and_required_regimes() -> None:
    domain = _report()["comparison_domain"]
    assert domain["case_count"] == 8
    assert tuple(domain["case_ids"]) == packet.CASE_IDS
    assert sum(row["comparison_role"] == "EXACT_STAGE_A_FAILURE_REPLAY" for row in domain["rows"]) == 3
    assert all(row["strictly_nonoverlapping"] for row in domain["rows"])
    roles = {role for row in domain["rows"] for role in row["roles"]}
    assert {
        "FAILED_STAGE_A_CONFIGURATION",
        "WIDE_SEPARATION",
        "SMALL_POSITIVE_GAP",
        "TRANSITION_DOMAIN",
        "LONG_RANGE",
        "LARGE_X",
        "SMALL_X",
    } <= roles


def test_order_component_and_atomic_cell_contract_is_exact() -> None:
    domain = _report()["comparison_domain"]
    assert domain["orders"] == [8, 16, 24, 32, 40, 48]
    assert domain["components"] == ["NEWTONIAN", "YUKAWA"]
    assert domain["component_count"] == 2
    assert domain["required_atomic_scientific_cells"] == 96
    assert domain["post_result_case_or_order_change"] == "FORBIDDEN"


def test_metrics_and_accuracy_rule_are_frozen() -> None:
    metrics = _report()["metric_contract"]
    assert metrics["oracle_floor_J"] == 1e-36
    assert metrics["accuracy_absolute_tolerance_J"] == 1e-36
    assert metrics["accuracy_relative_tolerance"] == 1e-6
    assert metrics["accuracy_rule"] == "absolute_error_J<=1e-36+1e-6*abs(U_oracle)"
    assert metrics["order_48_is_never_a_reference"] is True
    assert metrics["combined_energy_may_decide_component_accuracy"] is False
    assert metrics["convergence_ratio"].startswith("q_n=")


def test_all_nine_classification_predicates_are_preregistered() -> None:
    contract = _report()["classification_contract"]
    assert contract["multilabel_reporting_permitted"] is True
    assert contract["near_threshold_default"] == "PRODUCTION_FAILURE_NOT_LOCALIZED"
    assert set(contract["predicates"]) == {
        "PRODUCTION_CUBATURE_VALIDATED_ON_TESTED_CASES",
        "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
        "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED",
        "FIXED_ORDER_CUBATURE_INADEQUATE",
        "SLOW_BUT_CONVERGENT_AND_ECONOMICALLY_INFERIOR",
        "REGIME_DEPENDENT_PRODUCTION_FAILURE",
        "NEAR_CONTACT_OR_TRANSITION_REGIME_UNDERSAMPLED",
        "PRODUCTION_FAILURE_NOT_LOCALIZED",
        "PRODUCTION_COMPARISON_TIMEOUT",
    }
    assert contract["post_result_predicate_change"] == "FORBIDDEN"
    assert contract["visual_trend_classification"] == "FORBIDDEN"
    assert contract["favorable_rounding"] == "FORBIDDEN"


def test_ten_controls_use_the_live_comparison_pipeline() -> None:
    controls = _report()["controls"]
    assert controls["control_count"] == 10
    assert controls["all_use_production_comparison_pipeline"] is True
    assert [row["control_id"] for row in controls["rows"]] == [
        f"C{index:02d}_{suffix}"
        for index, suffix in enumerate((
            "POINT_EQUIVALENT_NEWTONIAN",
            "MISSING_A_Y_ONE_THIRD",
            "GAP_FOR_CENTER_DISTANCE",
            "RADIUS_AS_DIAMETER",
            "ONE_DIMENSION_UNREFINED",
            "WEIGHT_NORMALIZATION_BIAS",
            "COMPONENT_CHANNEL_SWAP",
            "ORDER_METADATA_OVERCLAIM",
            "ORACLE_OVERWRITE",
            "CONSTANT_MULTIPLICATIVE_BIAS",
        ), start=1)
    ]


def test_resource_envelope_is_coherent_and_fails_closed() -> None:
    resource = _report()["resource_and_custody_contract"]
    assert resource["maximum_total_wall_clock_seconds"] == 1200
    assert resource["maximum_memory_mib"] == 4096
    assert resource["per_order_cell_caps_seconds"] == {
        "8": 2, "16": 5, "24": 10, "32": 20, "40": 40, "48": 60
    }
    assert len(resource["stage_caps"]) == 6
    assert resource["sum_of_stage_caps_seconds"] == 1120
    assert resource["sum_of_stage_caps_seconds"] <= resource[
        "maximum_total_wall_clock_seconds"
    ]
    assert resource["process_group_termination"] == "MANDATORY"
    assert resource["zero_surviving_processes"] == "REQUIRED"
    assert resource["budget_exhaustion_behavior"] == (
        "FAIL_CLOSED_PRODUCTION_COMPARISON_TIMEOUT"
    )


def test_packet_review_outcomes_and_all_gates_are_exact() -> None:
    report = _report()
    assert report["packet_review_outcomes"] == [
        "PRODUCTION_COMPARISON_CONTRACT_READY",
        "BLOCKED_PRODUCTION_PATH_IDENTITY",
        "BLOCKED_ORACLE_CUSTODY",
        "BLOCKED_CASE_GRID_CONTRACT",
        "BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT",
        "BLOCKED_MUTATION_ROUTING",
        "BLOCKED_RESOURCE_OR_CUSTODY_CONTRACT",
        "BLOCKED_SCOPE_OR_PROVENANCE",
    ]
    gates = report["packet_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 36
    assert gates["failure_count"] == 0


def test_packet_prepares_no_execution_or_downstream_work() -> None:
    scope = _report()["scope"]
    assert scope["comparison_packet_prepared"] is True
    for key, value in scope.items():
        if key != "comparison_packet_prepared":
            assert value is False, key
    authority = _report()["authority"]
    assert authority["authorized_comparison_execution_count_after_review"] == 1
    assert authority["performed_comparison_execution_count"] == 0


def test_human_packet_records_contract_and_authority_ceiling() -> None:
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "96 required scientific cells",
        "8, 16, 24, 32, 40, 48",
        "not represented as a previously produced Stage A",
        "PRODUCTION_FAILURE_NOT_LOCALIZED",
        "1200 seconds",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
