from __future__ import annotations

import hashlib
import inspect
import json
from pathlib import Path

import pytest

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v2 as packet_v2,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet_v2.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _packet() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    first = packet_v2.artifact_bytes()
    second = packet_v2.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_build_preserves_every_authority_and_source_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in packet_v2.AUTHORITY_AND_SOURCE_HASHES
    }
    packet_v2.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in packet_v2.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == packet_v2.AUTHORITY_AND_SOURCE_HASHES


def test_v2_consumes_exact_blocked_v1_review_and_stops_at_review() -> None:
    packet = _packet()
    assert packet["target"] == packet_v2.TARGET
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == packet_v2.SELECTED_NEXT_TARGET
    assert packet["authority"]["consumed_v1_review_verdict"] == (
        "BLOCKED_SEMANTIC_ROUND_TRIP_PRODUCTION_CONTRACT_INCOMPLETE"
    )


def test_typed_ast_is_bounded_and_not_a_text_replacement_engine() -> None:
    typed = _packet()["typed_bounded_ast"]
    assert typed["node_types"] == [
        "Literal",
        "Symbol",
        "Constant",
        "Index",
        "Indexed",
        "Product",
        "Sum",
        "Power",
        "Derivative",
        "Equality",
    ]
    assert typed["arbitrary_text_replacement_used"] is False
    assert typed["general_tensor_algebra_claimed"] is False
    assert typed["general_equation_parser_built"] is False


def test_public_restore_does_not_accept_an_expected_target_result() -> None:
    signature = inspect.signature(packet_v2.restore)
    assert "expected_si_ast" not in signature.parameters
    assert "source_ast" in signature.parameters
    assert "convention_state" in signature.parameters
    assert "binding_id" in signature.parameters


def test_all_six_forward_transforms_are_computed_and_trace_every_rule() -> None:
    block = _packet()["computed_production_round_trips"]
    assert block["required_count"] == 6
    assert block["forward_computed_count"] == 6
    assert block["expected_target_comparison_count"] == 6
    for row in block["rows"]:
        contract = packet_v2.CONTRACTS[row["equation_id"]]
        trace = "\n".join(row["forward_rule_trace"])
        for rule_id in contract.required_forward_rule_ids:
            assert f"APPLIED:{rule_id}" in trace
        assert row["computed_si_ast"] == row["expected_si_oracle_ast"]


def test_all_six_inverse_transforms_consume_forward_lineage_and_round_trip() -> None:
    block = _packet()["computed_production_round_trips"]
    assert block["inverse_from_forward_output_count"] == 6
    assert block["semantic_round_trip_count"] == 6
    for row in block["rows"]:
        assert row["inverse_computed_from_forward_output"] is True
        assert row["inverse_passed"] is True
        assert row["semantic_round_trip_passed"] is True
        assert any(
            item == f"LINEAGE:CONSUMED_FORWARD_RESULT:{row['forward_lineage_id']}"
            for item in row["inverse_rule_trace"]
        )


def test_exact_T_psi_identity_is_preserved_without_generic_adapter() -> None:
    packet = _packet()
    bindings = packet["six_source_bindings"]
    assert bindings["exact_T_psi_route"] is True
    assert bindings["T_matter_adapter_used"] is False
    contract = packet_v2.CONTRACTS["MATTER_STRESS_ENERGY_EXCHANGE"]
    source_text = packet_v2.canonical(contract.source_ast)
    target_text = packet_v2.canonical(contract.expected_si_ast)
    assert "T_psi" in source_text and "T_psi" in target_text
    assert "T_matter" not in source_text and "T_matter" not in target_text


def test_quantum_round_trip_actually_applies_hbar_c_and_inverse_rules() -> None:
    quantum = _packet()["quantum_production_round_trip"]
    assert quantum["hbar_c_scale_applied"] is True
    assert quantum["forward_passed"] is True
    assert quantum["inverse_passed"] is True
    assert quantum["passed"] is True
    forward = "\n".join(quantum["forward_trace"])
    inverse = "\n".join(quantum["inverse_trace"])
    assert "APPLIED:MAP_M_STAR_TO_MC_OVER_HBAR" in forward
    assert "APPLIED:RESTORE_HBAR_C_DIRAC_SCALE" in forward
    assert "APPLIED:SUPPRESS_M_SI_TO_HBAR_MSTAR_OVER_C" in inverse


def test_all_eight_convention_mutations_fail_in_public_restore_before_output() -> None:
    controls = _packet()["production_convention_negative_controls"]
    assert controls["required_count"] == 8
    assert controls["exact_first_diagnostic_count"] == 8
    assert controls["all_failed_before_output"] is True
    assert len(controls["rows"]) == 8
    assert all(row["changed_field_count"] == 1 for row in controls["rows"])
    assert all(
        row["expected_first_diagnostic"] == row["observed_first_diagnostic"]
        and not row["output_emitted_before_failure"]
        for row in controls["rows"]
    )


def test_all_ten_production_adversarial_controls_pass_exactly() -> None:
    controls = _packet()["production_contract_adversarial_controls"]
    assert controls["required_count"] == 10
    assert controls["passed_count"] == 10
    assert len(controls["rows"]) == 10
    assert all(row["passed"] for row in controls["rows"])
    assert all(
        row["expected_first_diagnostic"] == row["observed_first_diagnostic"]
        for row in controls["rows"]
    )


def test_wrong_si_oracle_does_not_change_computed_maxwell_output() -> None:
    row = next(
        row
        for row in _packet()["production_contract_adversarial_controls"]["rows"]
        if row["mutation_id"] == "ADV_WRONG_SI_ORACLE"
    )
    assert row["computed_output_unchanged_by_oracle"] is True
    assert row["observed_first_diagnostic"] == "EXPECTED_TARGET_MISMATCH"
    assert row["passed"] is True


def test_missing_and_mutated_object_maps_cannot_report_success() -> None:
    rows = {
        row["mutation_id"]: row
        for row in _packet()["production_contract_adversarial_controls"]["rows"]
    }
    assert rows["ADV_REQUIRED_MAP_REMOVED"]["observed_first_diagnostic"] == (
        "REQUIRED_OBJECT_MAP_MISSING"
    )
    assert rows["ADV_OBJECT_MAP_MUTATED"]["observed_first_diagnostic"] == (
        "EXPECTED_TARGET_MISMATCH"
    )


def test_public_restore_enforces_preflight_without_manual_validator_call() -> None:
    contract = packet_v2.CONTRACTS["SOURCED_MAXWELL"]
    state = dict(packet_v2.BASE_CONVENTION_STATE)
    state["partial_0"] = "partial_t"
    with pytest.raises(packet_v2.ProductionContractError) as captured:
        packet_v2.restore(
            contract.equation_id,
            contract.source_ast,
            convention_state=state,
            binding_id=contract.binding_id,
        )
    assert captured.value.diagnostic == "PARTIAL0_MISSING_C_INVERSE"


def test_undeclared_Tmatter_and_invalid_adapter_fail_closed() -> None:
    rows = {
        row["mutation_id"]: row
        for row in _packet()["production_contract_adversarial_controls"]["rows"]
    }
    assert rows["ADV_T_PSI_REPLACED_BY_T_MATTER"]["observed_first_diagnostic"] == (
        "SOURCE_OBJECT_IDENTITY_MISMATCH"
    )
    assert rows["ADV_INVALID_ADAPTER"]["observed_first_diagnostic"] == (
        "ADAPTER_VALIDATION_FAILURE"
    )


def test_untrusted_pass_summary_and_stored_target_suppression_are_rejected() -> None:
    rows = {
        row["mutation_id"]: row
        for row in _packet()["production_contract_adversarial_controls"]["rows"]
    }
    forced = rows["ADV_FORCED_PASS_SUMMARY"]
    assert forced["untrusted_summary_ignored"] is True
    assert forced["observed_first_diagnostic"] == "EXPECTED_TARGET_MISMATCH"
    stored = rows["ADV_SUPPRESS_STORED_TARGET_WITHOUT_LINEAGE"]
    assert stored["observed_first_diagnostic"] == "LINEAGE_PROVENANCE_FAILURE"


def test_partial_quantum_restore_without_hbar_has_exact_diagnostic() -> None:
    row = next(
        row
        for row in _packet()["production_contract_adversarial_controls"]["rows"]
        if row["mutation_id"] == "ADV_QUANTUM_HBAR_OMITTED"
    )
    assert row["observed_first_diagnostic"] == "QUANTUM_HBAR_RESTORATION_MISSING"
    assert row["passed"] is True


def test_scope_blocks_authoritative_restoration_migration_and_adjacent_work() -> None:
    scope = _packet()["scope"]
    assert scope["v2_packet_preparation_only"] is True
    assert scope["authoritative_equation_restoration_executed"] is False
    assert scope["scientific_equation_migration_executed"] is False
    assert scope["authoritative_sources_modified"] is False
    assert scope["historical_artifacts_modified"] is False
    assert scope["repository_wide_rewrite_authorized"] is False
    assert scope["r13_reopened"] is False
    assert scope["external_comparator_activated"] is False
    assert scope["automation_created"] is False


def test_hard_stop_requires_independent_review_before_restoration_application() -> None:
    packet = _packet()
    hard_stop = packet["hard_stop"]
    assert hard_stop["independent_packet_review_required"] is True
    assert hard_stop["bounded_restoration_application_authorized_now"] is False
    assert hard_stop["migration_authorized_now"] is False
    assert "No migration" in packet["claim_ceiling"]
