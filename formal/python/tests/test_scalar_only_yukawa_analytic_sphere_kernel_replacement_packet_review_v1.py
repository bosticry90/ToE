from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v1 as review


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_exact_v1_packet() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_all_fifty_one_v0_passes_are_preserved() -> None:
    frozen = _report()["frozen_gate_audit"]
    assert frozen["accepted_v0_gate_count"] == 51
    assert frozen["preserved_count"] == 51
    assert frozen["altered_or_weakened_gate_ids"] == []
    assert frozen["custody_result"] == "PASS"


def test_six_repairs_are_accepted() -> None:
    accepted = _report()["accepted_v1_repairs"]
    assert set(accepted.values()) == {"ACCEPTED"}
    assert set(_report()["repair_audit"]["passed_repair_gate_ids"]) == {
        "R32_INTERNAL_REPLACEMENT_TARGETS_EXACT",
        "R33_LAMBDA_COMPONENT_COMPATIBILITY_MATRIX_COMPLETE",
        "R34_ARRAY_DOMAIN_FAILURE_SEMANTICS_COMPLETE",
        "R37_EIGHT_REGRESSION_INPUT_RECORDS_COMPLETE",
        "R40_INDEPENDENT_RADIAL_DERIVATIVE_REFERENCE_COMPLETE",
        "R50_RUNTIME_PROBE_INPUTS_EXACT",
    }


def test_capability_route_is_named_but_not_executable() -> None:
    audit = _report()["repair_audit"]
    assert audit["validation_hook_missing_fields"] == [
        "capability_constructor_visibility", "capability_issuer",
        "capability_process_scope", "capability_validation_failure",
        "mutation_id_binding", "private_entrypoint_signature",
    ]


def test_limit_probes_lack_typed_adjudicators_and_complete_p13_inputs() -> None:
    audit = _report()["repair_audit"]
    assert len(audit["incomplete_probe_ids"]) == 13
    assert audit["p13_complete_public_inputs"] is False


def test_mutation_routes_and_predicates_remain_nonexecutable() -> None:
    audit = _report()["repair_audit"]
    assert audit["mutation_route_complete_count"] == 0
    assert audit["mutation_predicate_complete_count"] == 0
    assert audit["static_scanner_complete"] is False


def test_root_encoding_is_fixed_but_nested_schema_is_absent() -> None:
    missing = _report()["repair_audit"]["serialization_missing_nested_schema_fields"]
    assert missing == [
        "custody_schema", "duplicate_key_parser", "limit_row_schema",
        "mutation_row_schema", "regression_row_schema", "runtime_schema",
        "status_enum", "terminal_outcome_enum",
    ]


def test_exact_five_failed_gates_and_counts() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 62
    assert gates["pass_count"] == 57
    assert gates["failure_count"] == 5
    assert gates["failed_gate_ids"] == list(review.FAILED_GATE_IDS)


def test_outcome_and_fresh_selector_are_exact() -> None:
    report = _report()
    assert report["principal_review_outcome"] == "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE"
    assert report["secondary_review_outcomes"] == [
        "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
        "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
    ]
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    action = report["required_next_action"]
    assert action["fresh_selector_required"] is True
    assert action["silent_correction"] == "PROHIBITED"
    assert action["automatic_v2"] == "PROHIBITED"


def test_review_authorizes_no_implementation_or_downstream_work() -> None:
    scope = _report()["scope"]
    assert scope["independent_v1_review_performed"] is True
    assert scope["fresh_scientific_response_selector_authorized"] is True
    for key in (
        "replacement_contract_ready", "candidate_kernel_creation_authorized",
        "candidate_kernel_created", "candidate_kernel_execution_authorized",
        "candidate_kernel_executed", "production_source_or_dispatch_change_authorized",
        "shadow_qualification_authorized", "old_cubature_called",
        "old_cubature_adjudicated", "silent_correction_authorized",
        "automatic_v2_authorized", "stage_a_rerun_authorized",
        "torque_or_dft_authorized", "jacobian_or_identifiability_authorized",
        "stage_b_authorized",
    ):
        assert scope[key] is False


def test_human_review_records_narrow_block_and_authority() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT, "57 PASS / 5 FAIL", "51 frozen gates remain preserved",
        "Six repairs pass", "Five repairs remain blocked",
        "No candidate kernel was created or executed", review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
