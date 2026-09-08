from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_v0 as packet


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_consumes_exact_selector() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["authority"]["consumed_selector_route"] == (
        "ISOLATE_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE"
    )


def test_terminal_boundary_has_no_repair_or_regress() -> None:
    boundary = _report()["terminal_governance_boundary"]
    assert boundary["packet_version"] == "V0_ONLY"
    assert boundary["repair_version"] == "PROHIBITED"
    assert boundary["prerequisite_to_prerequisite"] == "PROHIBITED"
    assert boundary["review_outcomes"] == list(packet.REVIEW_OUTCOMES)
    assert len(boundary["ready_review_next_selector_options_exact"]) == 2
    assert len(boundary["failed_review_next_selector_options_exact"]) == 2


def test_capability_protocol_is_process_scoped_and_executable() -> None:
    capability = _report()["capability_protocol_v0"]
    assert "anonymous_pipe" in capability["session_constructor"]
    assert "issue_capability" in capability["issuer_entrypoint"]
    assert capability["public_entrypoint_signature"] == (
        "evaluate_fixture(fixture_id,input_record_id)->FixtureResultV0"
    )
    assert "capability" in capability["private_entrypoint_signature"]
    assert len(capability["token_schema"]["fields"]) == 10
    assert len(capability["manifest_schema"]["fields"]) == 7
    assert capability["pipe_frame"].startswith("UINT32_BIG_ENDIAN")
    assert len(capability["authentication_order"]) == 11
    assert len(capability["error_enum"]) == 11
    assert capability["ambient_environment_or_global_validation_mode"] == "FORBIDDEN"


def test_typed_predicate_schemas_and_algorithms_are_complete() -> None:
    contract = _report()["typed_adjudicator_contract_v0"]
    assert set(contract["schema_registry"]) == {
        "NumericPredicateV0", "ExceptionPredicateV0", "RelationalPredicateV0",
        "DependencyPredicateV0", "AdjudicationResultV0",
    }
    assert contract["predicate_kind_enum"] == [
        "NUMERIC", "EXCEPTION", "RELATIONAL", "DEPENDENCY",
    ]
    assert set(contract["numeric_algorithms"]) == {
        "ABS_REL_LE", "RELATIVE_DIFFERENCE_GE", "EXACT_FLOAT_HEX",
    }
    assert len(contract["predicate_rows"]) == 9


def test_eight_kernel_free_fixtures_are_fully_bound() -> None:
    fixtures = _report()["synthetic_fixture_contract_v0"]
    assert fixtures["fixture_count"] == 8
    assert fixtures["kernel_or_physics_imports"] == "FORBIDDEN"
    assert fixtures["all_values_are_synthetic"] is True
    required = {"fixture_id", "entrypoint", "input_record_id", "inputs", "baseline_contract", "expected"}
    assert all(required <= set(row) for row in fixtures["fixture_rows"])


def test_every_mutation_route_binds_complete_execution_path() -> None:
    report = _report()
    contract = report["mutation_routing_contract_v0"]
    assert contract["route_count"] == 8
    required = {
        "route_id", "fixture_id", "input_record_id", "public_baseline_call",
        "private_mutated_call", "mutation_id", "injection_point",
        "capability_binding", "adjudicator_entrypoint", "predicate_id",
        "execution_order", "failure_consequence",
    }
    assert all(required <= set(row) for row in contract["route_rows"])
    assert all(row["capability_binding"]["single_use"] is True for row in contract["route_rows"])
    fixture_rows = report["synthetic_fixture_contract_v0"]["fixture_rows"]
    fixture_inputs = {(row["fixture_id"], row["input_record_id"]) for row in fixture_rows}
    predicate_ids = {
        row["predicate_id"]
        for row in report["typed_adjudicator_contract_v0"]["predicate_rows"]
    }
    assert all((row["fixture_id"], row["input_record_id"]) in fixture_inputs for row in contract["route_rows"])
    assert all(row["predicate_id"] in predicate_ids for row in contract["route_rows"])


def test_dependency_scanner_contract_is_executable() -> None:
    scanner = _report()["dependency_scanner_contract_v0"]
    assert len(scanner["source_roots"]) == 2
    assert set(scanner["source_roots"]) == set(scanner["virtual_sources"])
    assert scanner["forbidden_modules"] == ["forbidden_oracle", "forbidden_cubature"]
    assert "__import__" in scanner["dynamic_import_rule"]
    assert len(scanner["expected_bad_source_violations"]) == 2


def test_recursive_schemas_enums_and_duplicate_parser_are_exact() -> None:
    contract = _report()["recursive_canonical_schema_contract_v0"]
    assert set(contract["schema_registry"]) == {
        "QualificationResultV0", "RunRecordV0", "CapabilityResultV0",
        "FixtureResultV0", "ExceptionRecordV0", "MutationResultV0",
        "DependencyScanResultV0", "SerializationResultV0",
    }
    assert len(contract["enum_registry"]) == 6
    assert "object_pairs_hook=reject_duplicate_pairs" in contract["strict_parser"]
    assert "sort_keys=True" in contract["canonical_encoder"]
    assert contract["binary64_rule"].startswith("LOWERCASE")


def test_future_controls_are_mandatory_but_not_executed() -> None:
    controls = _report()["synthetic_qualification_controls_v0"]
    assert len(controls["control_order"]) == 12
    assert controls["all_controls_mandatory"] is True
    assert controls["total_wall_clock_seconds_max"] == 60
    assert controls["memory_mib_max"] == 256
    assert controls["execution_authorized_by_this_packet"] is False


def test_exploratory_sandbox_tier_is_lighter_but_not_authorized() -> None:
    tier = _report()["future_exploratory_sandbox_risk_tier"]
    assert tier["authorized_now"] is False
    assert tier["labels_exact"] == [
        "EXPLORATORY_IMPLEMENTATION_RESULT", "NON_PRODUCTION",
        "NON_ADJUDICATIVE", "NO_SCIENTIFIC_CLAIM",
    ]
    assert tier["may_change_production_or_issue_scientific_verdict"] is False


def test_scope_contains_no_implementation_or_scientific_execution() -> None:
    scope = _report()["scope"]
    assert scope["prerequisite_packet_prepared"] is True
    assert scope["independent_terminal_review_authorized"] is True
    for key in (
        "replacement_packet_v2_created", "replacement_packet_v2_authorized",
        "prerequisite_repair_version_authorized", "prerequisite_to_prerequisite_authorized",
        "infrastructure_implementation_created", "synthetic_fixture_execution_performed",
        "candidate_kernel_created", "candidate_kernel_executed",
        "shadow_qualification_authorized", "production_source_or_dispatch_changed",
        "old_cubature_called", "old_cubature_adjudicated", "stage_a_rerun_authorized",
        "torque_or_dft_authorized", "jacobian_or_identifiability_authorized",
        "stage_b_authorized",
    ):
        assert scope[key] is False


def test_packet_gate_count_and_human_boundary() -> None:
    report = _report()
    assert report["packet_gates"]["gate_count"] == 50
    assert report["packet_gates"]["pass_count"] == 50
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT, "V0 only", "No repair version", "eight synthetic fixtures",
        "twelve mandatory controls", "EXPLORATORY_IMPLEMENTATION_RESULT",
        "No infrastructure or kernel code was created", packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
