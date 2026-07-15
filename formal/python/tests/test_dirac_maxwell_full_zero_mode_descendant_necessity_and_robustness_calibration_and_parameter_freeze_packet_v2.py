from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2 as freeze
from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2 as classifier


ROOT = find_repo_root(Path(__file__))
PACKET_PATH = ROOT / freeze.PACKET_RELATIVE_PATH
MATRIX_PATH = ROOT / freeze.RUN_MATRIX_RELATIVE_PATH
IDENTITY_PATH = ROOT / freeze.OUTPUT_IDENTITY_RELATIVE_PATH
CLASSIFIER_PATH = ROOT / freeze.CLASSIFIER_RELATIVE_PATH


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture() -> tuple[dict, dict, dict, dict[str, dict]]:
    packet = _load(PACKET_PATH)
    matrix = _load(MATRIX_PATH)
    identity = _load(IDENTITY_PATH)
    thresholds = {item["raw_series_key"]: float(item["frozen_value"]) for item in packet["numerical_threshold_provenance"] if item["threshold_class"] != "NUMERICAL_FLOOR"}
    record_by_id = {item["run_id"]: item for item in matrix["records"]}
    outputs: dict[str, dict] = {}
    for expected in identity["outputs"]:
        record = record_by_id[expected["run_id"]]
        series = {key: [0.0, 0.1 * value] for key, value in thresholds.items()}
        series.update(
            {
                "solver_iterations": [4.0, 5.0],
                "final_phi2_l2": [1.0],
                "final_descendant_l2": [1.0],
                "matter_density_l2": [1.0, 1.0],
                "longitudinal_electric_field_l2": [1.0, 1.0],
                "matter_energy": [1.0, 1.0],
                "total_source_current_l2": [1.0, 1.0],
                "cumulative_exchange_longitudinal": [0.0, 1.0],
                "cumulative_exchange_phi2": [0.0, 0.01],
                "cumulative_exchange_phi3": [0.0, 0.01],
                "forced_transverse_equation_residual": [0.0, 1e-3],
            }
        )
        if record["run_role"] == "SPATIAL_REFINEMENT":
            series["final_phi2_l2"] = [1.0 + 1.0 / float(record["grid_size"])]
        if record["run_role"] == "TEMPORAL_REFINEMENT":
            dt = float(record["time_step"])
            series["final_descendant_l2"] = [1.0 + dt * dt]
            series["total_energy_delta"] = [0.0, 1e-6 * dt * dt]
        if record["run_role"] == "FORCED_COMPARATOR":
            series["matter_density_l2"] = [0.98, 0.98]
            series["longitudinal_electric_field_l2"] = [0.98, 0.98]
            series["matter_energy"] = [0.98, 0.98]
            series["total_source_current_l2"] = [0.98, 0.98]
            series["cumulative_exchange_longitudinal"] = [0.0, 0.98]
        control_observables: dict[str, float] = {}
        if "control_metadata" in record:
            for spec in record["control_metadata"]["control_evaluation_spec"]["required_observations"]:
                operator = spec["comparison_operator"]
                target = float(spec["target_value"])
                control_observables[spec["observable_id"]] = target if operator in {"GE", "GT", "EQ"} else min(0.0, target)
        payload = {
            "run_id": expected["run_id"],
            "scientific_row_id": expected["scientific_row_id"],
            "run_role": expected["run_role"],
            "model_class": expected["model_class"],
            "parent_run_or_row_id": expected["parent_run_or_row_id"],
            "input_hash": expected["input_hash"],
            "relative_output_path": expected["relative_output_path"],
            "series": series,
            "raw_observables": {"solver_error_norm": 1e-7, "truncation_error_norm": 1e-4, "model_domain_margin": 1.0},
            "control_observables": control_observables,
            "registered_numerical_payload": {"row_id": expected["scientific_row_id"], "samples": [1.0, 2.0, 3.0]},
        }
        outputs[expected["relative_output_path"]] = payload
    return packet, matrix, identity, outputs


def _classify(packet: dict, matrix: dict, identity: dict, outputs: dict[str, dict]) -> dict:
    return classifier.classify_registered_result(packet, matrix, identity, outputs, classifier_path=CLASSIFIER_PATH)


def _rebind_matrix(packet: dict, matrix: dict) -> None:
    packet["canonical_run_matrix"]["sha256"] = classifier.sha256_bytes(classifier.canonical_json_bytes(matrix))


def _rebind_identity(packet: dict, identity: dict) -> None:
    packet["expected_output_identity_manifest"]["sha256"] = classifier.sha256_bytes(classifier.canonical_json_bytes(identity))


def test_generated_artifacts_are_current() -> None:
    expected = freeze.artifact_bytes()
    assert all((ROOT / path).read_bytes() == raw for path, raw in expected.items())


def test_v2_preserves_exact_scope_and_corrects_only_contract_semantics() -> None:
    packet, matrix, identity, _ = _fixture()
    assert matrix["record_count"] == identity["record_count"] == 203
    assert matrix["scientific_record_count"] == 182
    assert matrix["control_record_count"] == 21
    assert matrix["role_counts"]["POSITIVE_CONTROL"] == 8
    assert matrix["role_counts"]["NEGATIVE_CONTROL"] == 13
    assert len(packet["numerical_threshold_provenance"]) == 22
    assert {item["threshold_id"]: item["frozen_value"] for item in packet["convergence_threshold_provenance"]} == {
        "minimum_spatial_descendant_order": 0.8,
        "minimum_temporal_descendant_order": 1.5,
        "minimum_energy_error_order": 1.5,
    }
    assert {item["threshold_id"]: item["expected_convergence_class"] for item in packet["convergence_threshold_provenance"]} == {
        "minimum_spatial_descendant_order": "FIRST_ORDER_WILSON_AFFECTED_SPATIAL",
        "minimum_temporal_descendant_order": "SECOND_ORDER_TEMPORAL",
        "minimum_energy_error_order": "SECOND_ORDER_ENERGY_ERROR",
    }
    assert packet["bounded_correction_scope"]["additional_pilot_required"] is False
    assert packet["authority_boundary"]["canonical_fourteen_row_execution_authorized"] is False


def test_every_threshold_has_complete_fail_closed_schema() -> None:
    packet, _, _, _ = _fixture()
    required = {
        "threshold_id", "observable_id", "raw_series_key", "threshold_class", "comparison_operator", "frozen_value",
        "expected_convergence_class", "eligible_run_roles", "eligible_scientific_rows", "units", "normalization_formula",
        "row_scaling_rule", "numerical_floor", "pilot_source_run_ids", "raw_pilot_values", "generation_formula",
        "safety_factor", "rounding_rule", "failure_diagnostic",
    }
    for threshold in packet["numerical_threshold_provenance"]:
        assert set(threshold) == required
        assert threshold["eligible_run_roles"]
        assert len(threshold["eligible_scientific_rows"]) == 14
        assert threshold["units"] and threshold["normalization_formula"] and threshold["row_scaling_rule"]
        assert threshold["pilot_source_run_ids"] and threshold["raw_pilot_values"]


def test_control_coverage_is_explicit_and_feature_appropriate() -> None:
    packet, matrix, _, _ = _fixture()
    contracts = packet["control_applicability_freeze"]["contracts"]
    assert len(contracts) == 21
    assert {item["scope_class"] for item in contracts} <= set(packet["control_applicability_freeze"]["scope_classes"])
    negatives = [record for record in matrix["records"] if record["run_role"] == "NEGATIVE_CONTROL"]
    assert {record["scientific_row_id"] for record in negatives} >= {"R00_CANONICAL", "R05_F_HIGH", "R10_MU_HIGH", "R11_CORNER_WEAK_HIGH"}
    assert all(record["control_metadata"]["representativeness_basis"] for record in negatives)


def test_filename_mapping_is_exact_bijection() -> None:
    _, _, identity, _ = _fixture()
    assert len(identity["run_id_to_safe_filename"]) == 203
    assert len(identity["safe_filename_to_run_id"]) == 203
    for run_id, filename in identity["run_id_to_safe_filename"].items():
        assert identity["safe_filename_to_run_id"][filename] == run_id


def test_raw_classifier_reconstructs_admissible_fixture() -> None:
    packet, matrix, identity, outputs = _fixture()
    result = _classify(packet, matrix, identity, outputs)
    assert result["execution_status"] == "CLASSIFIED_PENDING_INDEPENDENT_RESULT_REVIEW"
    assert result["robustness_status"] == "BROADLY_ROBUST"
    assert result["descendant_significance_status"] == "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL"
    assert result["scientific_claim_authorized"] is False
    spatial_orders = [item["minimum_spatial_descendant_order"] for item in result["observed_convergence_orders"].values()]
    assert min(spatial_orders) > 0.99


def test_numerical_block_suppresses_materiality() -> None:
    packet, matrix, identity, outputs = _fixture()
    record = next(item for item in matrix["records"] if item["run_role"] == "PRIMARY_FULL_MODEL")
    outputs[record["output_path"]]["series"]["solver_residual"] = [1.0]
    result = _classify(packet, matrix, identity, outputs)
    assert result["robustness_status"] == "NUMERICALLY_BLOCKED"
    assert result["descendant_significance_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"


def test_model_domain_block_suppresses_materiality() -> None:
    packet, matrix, identity, outputs = _fixture()
    record = next(item for item in matrix["records"] if item["run_role"] == "PRIMARY_FULL_MODEL")
    outputs[record["output_path"]]["raw_observables"]["model_domain_margin"] = -1e-3
    result = _classify(packet, matrix, identity, outputs)
    assert result["robustness_status"] == "MODEL_DOMAIN_LIMITED"
    assert result["descendant_significance_status"] == "NOT_EVALUATED_MODEL_DOMAIN_LIMIT"


def test_classifier_rejects_supplied_decisions_and_identity_defects_first() -> None:
    packet, matrix, identity, outputs = _fixture()
    first = next(iter(outputs.values()))
    first["passed"] = True
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_CLASSIFIER_TRUST"

    packet, matrix, identity, outputs = _fixture()
    outputs.pop(next(iter(outputs)))
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_RUN_IDENTITY"

    packet, matrix, identity, outputs = _fixture()
    first_path = next(iter(outputs))
    outputs[first_path]["run_id"] = "UNKNOWN_ROW"
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_RUN_IDENTITY"

    packet, matrix, identity, outputs = _fixture()
    outputs["formal/output/canonical/orphan.json"] = copy.deepcopy(next(iter(outputs.values())))
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_RUN_IDENTITY"


def test_convergence_class_mutations_have_exact_diagnostic() -> None:
    packet, matrix, identity, outputs = _fixture()
    spatial = next(item for item in packet["convergence_threshold_provenance"] if item["threshold_id"] == "minimum_spatial_descendant_order")
    spatial["frozen_value"] = 1.5
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH"

    packet, matrix, identity, outputs = _fixture()
    temporal = next(item for item in packet["convergence_threshold_provenance"] if item["threshold_id"] == "minimum_temporal_descendant_order")
    temporal["expected_convergence_class"] = "FIRST_ORDER_WILSON_AFFECTED_SPATIAL"
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH"


def test_threshold_scope_mutations_have_exact_diagnostics() -> None:
    packet, matrix, identity, outputs = _fixture()
    del packet["numerical_threshold_provenance"][0]["units"]
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_THRESHOLD_SCHEMA"

    packet, matrix, identity, outputs = _fixture()
    threshold = next(item for item in packet["numerical_threshold_provenance"] if item["threshold_id"] == "maximum_phi2_wave_residual")
    threshold["eligible_run_roles"].append("FORCED_COMPARATOR")
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_THRESHOLD_SCOPE"

    packet, matrix, identity, outputs = _fixture()
    packet["numerical_threshold_provenance"][0]["row_scaling_rule"] = ""
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_THRESHOLD_SCOPE"


def test_control_applicability_and_filename_mutations_have_exact_diagnostics() -> None:
    packet, matrix, identity, outputs = _fixture()
    control = next(item for item in matrix["records"] if item["run_role"] == "NEGATIVE_CONTROL")
    control["control_metadata"]["scope_class"] = "GLOBAL_IMPLEMENTATION_INVARIANT"
    _rebind_matrix(packet, matrix)
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_CONTROL_SCHEMA"

    packet, matrix, identity, outputs = _fixture()
    identity.pop("safe_filename_to_run_id")
    _rebind_identity(packet, identity)
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_RUN_IDENTITY"

    packet, matrix, identity, outputs = _fixture()
    identity["outputs"][1]["safe_filename"] = identity["outputs"][0]["safe_filename"]
    identity["run_id_to_safe_filename"][identity["outputs"][1]["run_id"]] = identity["outputs"][0]["safe_filename"]
    identity["safe_filename_to_run_id"][identity["outputs"][0]["safe_filename"]] = identity["outputs"][1]["run_id"]
    _rebind_identity(packet, identity)
    assert _classify(packet, matrix, identity, outputs)["execution_status"] == "B-BLOCKED_RUN_IDENTITY"


def test_all_permanent_blocker_mutations_are_registered_once() -> None:
    packet, _, _, _ = _fixture()
    mutations = packet["blocker_regression_mutations"]
    assert len(mutations) == 23
    assert len({item["mutation_id"] for item in mutations}) == 23
    assert all(item["expected_exact_diagnostic"] and item["unrelated_prior_failure_forbidden"] == "true" for item in mutations)


MUTATION_IDS = [
    "M_V2_SPATIAL_FLOOR_REVERTED_TO_1P5",
    "M_V2_TEMPORAL_FLOOR_CHANGED_TO_0P8",
    "M_V2_EXPECTED_ORDER_METADATA_REMOVED",
    "M_V2_THRESHOLD_ELIGIBLE_ROLES_REMOVED",
    "M_V2_THRESHOLD_UNITS_REMOVED",
    "M_V2_THRESHOLD_NORMALIZATION_REMOVED",
    "M_V2_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY",
    "M_V2_UNSCALED_ABSOLUTE_THRESHOLD_SUBSTITUTED",
    "M_V2_SUPPLIED_PASSED_TRUE_WITH_RAW_FAILURE",
    "M_V2_UNKNOWN_RUN_ID_ADDED",
    "M_V2_REQUIRED_RUN_OMITTED",
    "M_V2_VALID_RUN_DUPLICATED_UNDER_NEW_ID",
    "M_V2_MATERIALITY_SUPPLIED_AFTER_NUMERICAL_BLOCK",
    "M_V2_RAW_OUTPUT_CHANGED_SUMMARY_UNCHANGED",
    "M_V2_PHASE_CONTROL_MARKED_GLOBAL",
    "M_V2_HOLONOMY_CONTROL_ON_TRIVIAL_ONLY_ROW",
    "M_V2_REPRESENTATIVE_BASIS_REMOVED",
    "M_V2_CORNER_RELEVANT_CONTROL_EXCLUDED",
    "M_V2_INVERSE_FILENAME_MAPPING_REMOVED",
    "M_V2_TWO_IDS_ONE_FILENAME",
    "M_V2_WRONG_PAYLOAD_RUN_ID",
    "M_V2_FILE_RENAMED_PAYLOAD_UNCHANGED",
    "M_V2_ORPHAN_OUTPUT_ADDED",
]


@pytest.mark.parametrize("mutation_id", MUTATION_IDS)
def test_every_blocker_mutation_produces_only_its_registered_diagnostic(mutation_id: str) -> None:
    packet, matrix, identity, outputs = _fixture()
    registered = {item["mutation_id"]: item["expected_exact_diagnostic"] for item in packet["blocker_regression_mutations"]}
    if mutation_id == "M_V2_SPATIAL_FLOOR_REVERTED_TO_1P5":
        next(item for item in packet["convergence_threshold_provenance"] if item["threshold_id"] == "minimum_spatial_descendant_order")["frozen_value"] = 1.5
    elif mutation_id == "M_V2_TEMPORAL_FLOOR_CHANGED_TO_0P8":
        next(item for item in packet["convergence_threshold_provenance"] if item["threshold_id"] == "minimum_temporal_descendant_order")["frozen_value"] = 0.8
    elif mutation_id == "M_V2_EXPECTED_ORDER_METADATA_REMOVED":
        del packet["convergence_threshold_provenance"][0]["expected_convergence_class"]
    elif mutation_id == "M_V2_THRESHOLD_ELIGIBLE_ROLES_REMOVED":
        del packet["numerical_threshold_provenance"][0]["eligible_run_roles"]
    elif mutation_id == "M_V2_THRESHOLD_UNITS_REMOVED":
        del packet["numerical_threshold_provenance"][0]["units"]
    elif mutation_id == "M_V2_THRESHOLD_NORMALIZATION_REMOVED":
        del packet["numerical_threshold_provenance"][0]["normalization_formula"]
    elif mutation_id == "M_V2_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY":
        threshold = next(item for item in packet["numerical_threshold_provenance"] if item["threshold_id"] == "maximum_phi2_wave_residual")
        threshold["eligible_run_roles"].append("FORCED_COMPARATOR")
    elif mutation_id == "M_V2_UNSCALED_ABSOLUTE_THRESHOLD_SUBSTITUTED":
        packet["numerical_threshold_provenance"][0]["row_scaling_rule"] = ""
    elif mutation_id == "M_V2_SUPPLIED_PASSED_TRUE_WITH_RAW_FAILURE":
        next(iter(outputs.values()))["passed"] = True
    elif mutation_id == "M_V2_UNKNOWN_RUN_ID_ADDED":
        next(iter(outputs.values()))["run_id"] = "R99_UNKNOWN"
    elif mutation_id == "M_V2_REQUIRED_RUN_OMITTED":
        outputs.pop(next(iter(outputs)))
    elif mutation_id == "M_V2_VALID_RUN_DUPLICATED_UNDER_NEW_ID":
        outputs["formal/output/canonical/duplicate-valid-run.json"] = copy.deepcopy(next(iter(outputs.values())))
    elif mutation_id == "M_V2_MATERIALITY_SUPPLIED_AFTER_NUMERICAL_BLOCK":
        payload = next(iter(outputs.values()))
        payload["materiality_class"] = "DESCENDANT_DOMINATED_REGIME"
        payload["series"]["solver_residual"] = [1.0]
    elif mutation_id == "M_V2_RAW_OUTPUT_CHANGED_SUMMARY_UNCHANGED":
        primary = next(item for item in matrix["records"] if item["run_role"] == "PRIMARY_FULL_MODEL")
        outputs[primary["output_path"]]["series"]["solver_residual"] = [1.0]
    elif mutation_id in {
        "M_V2_PHASE_CONTROL_MARKED_GLOBAL",
        "M_V2_HOLONOMY_CONTROL_ON_TRIVIAL_ONLY_ROW",
        "M_V2_REPRESENTATIVE_BASIS_REMOVED",
        "M_V2_CORNER_RELEVANT_CONTROL_EXCLUDED",
    }:
        if mutation_id == "M_V2_PHASE_CONTROL_MARKED_GLOBAL":
            control = next(item for item in matrix["records"] if item["run_id"].endswith("P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED"))
            control["control_metadata"]["scope_class"] = "GLOBAL_IMPLEMENTATION_INVARIANT"
        elif mutation_id == "M_V2_HOLONOMY_CONTROL_ON_TRIVIAL_ONLY_ROW":
            control = next(item for item in matrix["records"] if item["run_id"].endswith("P_PHI2_PHI3_INTERCHANGE"))
            control["control_metadata"]["representative_row_id"] = "R06_THETA_TRIVIAL"
        elif mutation_id == "M_V2_REPRESENTATIVE_BASIS_REMOVED":
            control = next(item for item in matrix["records"] if item["run_role"] == "NEGATIVE_CONTROL")
            control["control_metadata"]["representativeness_basis"] = ""
        else:
            control = next(item for item in matrix["records"] if item["run_id"].endswith("N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL"))
            control["control_metadata"]["applicable_row_ids"].remove("R11_CORNER_WEAK_HIGH")
        _rebind_matrix(packet, matrix)
    elif mutation_id == "M_V2_INVERSE_FILENAME_MAPPING_REMOVED":
        identity.pop("safe_filename_to_run_id")
        _rebind_identity(packet, identity)
    elif mutation_id == "M_V2_TWO_IDS_ONE_FILENAME":
        first, second = identity["outputs"][:2]
        second["safe_filename"] = first["safe_filename"]
        identity["run_id_to_safe_filename"][second["run_id"]] = first["safe_filename"]
        identity["safe_filename_to_run_id"][first["safe_filename"]] = second["run_id"]
        _rebind_identity(packet, identity)
    elif mutation_id == "M_V2_WRONG_PAYLOAD_RUN_ID":
        next(iter(outputs.values()))["run_id"] = "WRONG_INTERNAL_RUN_ID"
    elif mutation_id == "M_V2_FILE_RENAMED_PAYLOAD_UNCHANGED":
        old_path = next(iter(outputs))
        outputs[old_path + ".renamed"] = outputs.pop(old_path)
    elif mutation_id == "M_V2_ORPHAN_OUTPUT_ADDED":
        outputs["formal/output/canonical/orphan.json"] = copy.deepcopy(next(iter(outputs.values())))
    else:
        raise AssertionError(f"unimplemented mutation {mutation_id}")

    result = _classify(packet, matrix, identity, outputs)
    observed = result["robustness_status"] if mutation_id == "M_V2_RAW_OUTPUT_CHANGED_SUMMARY_UNCHANGED" else result["execution_status"]
    assert observed == registered[mutation_id]
