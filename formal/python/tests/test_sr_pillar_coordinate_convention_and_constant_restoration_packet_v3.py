from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v3 as packet_v3,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet_v3.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _packet() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _control(mutation_id: str) -> dict[str, object]:
    rows = _packet()["production_contract_adversarial_controls"]["rows"]
    return next(row for row in rows if row["mutation_id"] == mutation_id)


def test_packet_regenerates_exactly_and_deterministically() -> None:
    first = packet_v3.artifact_bytes()
    second = packet_v3.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_packet_preserves_every_frozen_authority_and_source_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in packet_v3.AUTHORITY_AND_SOURCE_HASHES
    }
    packet_v3.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in packet_v3.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == packet_v3.AUTHORITY_AND_SOURCE_HASHES


def test_packet_consumes_v2_block_and_stops_for_independent_v3_review() -> None:
    packet = _packet()
    assert packet["target"] == packet_v3.TARGET
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == packet_v3.SELECTED_NEXT_TARGET
    assert packet["authority"]["consumed_v2_review_verdict"] == (
        "BLOCKED_CANONICALIZATION_AND_LINEAGE_CONTRACT_UNSOUND"
    )


def test_physical_convention_and_six_source_bindings_are_retained() -> None:
    packet = _packet()
    convention = packet["retained_physical_convention"]
    assert convention["temporal_coordinate"] == "x^0=c t"
    assert convention["metric_signature"] == "(+,-,-,-)"
    assert convention["restoration_target"] == "SI"
    assert convention["reconsidered_in_v3"] is False
    bindings = packet["six_source_bindings"]
    assert bindings["validated_count"] == bindings["required_count"] == 6
    assert bindings["exact_T_psi_route"] is True
    assert bindings["T_matter_adapter_used"] is False


def test_ast_distinguishes_scalar_operator_application_and_derivative_nodes() -> None:
    nodes = _packet()["typed_bounded_ast"]["node_types"]
    for required in ("ScalarProduct", "OperatorProduct", "Apply", "Derivative"):
        assert required in nodes
    assert _packet()["typed_bounded_ast"]["general_tensor_algebra_claimed"] is False


def test_whitelisted_scalar_reordering_passes_but_operator_order_does_not() -> None:
    audit = _packet()["operator_aware_canonicalization"]
    assert audit["passed_count"] == audit["required_count"] == 4
    assert audit["checks"] == {
        "derivative_application_scope_preserved": True,
        "gamma_D_and_D_gamma_ast_nodes_are_ordered": True,
        "operator_order_preserved": True,
        "safe_scalar_constants_commute": True,
    }
    assert audit["global_product_commutativity_assumed"] is False
    assert audit["registered_commutation_theorems"] == []


def test_operator_objects_cannot_be_smuggled_into_scalar_product() -> None:
    gamma = packet_v3.V("gamma", "SI", packet_v3.MU_U)
    dop = packet_v3.V("D", "SI", packet_v3.MU_D)
    with pytest.raises(ValueError, match="OPERATOR_IN_SCALAR_PRODUCT"):
        packet_v3.canonical(packet_v3.ScalarProduct((gamma, dop)))


def test_quantum_source_uses_ordered_operator_application() -> None:
    source = _packet()["quantum_production_round_trip"]["source_ast"]
    encoded = json.dumps(source, sort_keys=True)
    assert '"node": "operator_product"' in encoded
    assert '"node": "apply"' in encoded
    gamma_position = encoded.index('"object_id": "gamma"')
    derivative_position = encoded.index('"object_id": "D"')
    assert gamma_position < derivative_position


def test_all_six_forward_oracle_inverse_and_semantic_round_trips_pass() -> None:
    result = _packet()["computed_production_round_trips"]
    assert result["required_count"] == 6
    assert result["forward_computed_count"] == 6
    assert result["expected_target_comparison_count"] == 6
    assert result["inverse_from_forward_output_count"] == 6
    assert result["semantic_round_trip_count"] == 6
    assert all(row["semantic_round_trip_passed"] for row in result["rows"])


def test_exact_restore_issued_object_is_accepted_for_suppression() -> None:
    packet_v3._reset_issuance_registry_for_packet_build()
    contract = packet_v3.CONTRACTS["SOURCED_MAXWELL"]
    forward = packet_v3.restore(
        contract.equation_id,
        contract.source_ast,
        convention_state=dict(packet_v3.BASE_CONVENTION_STATE),
        binding_id=contract.binding_id,
    )
    inverse = packet_v3.suppress(
        forward,
        convention_state=dict(packet_v3.BASE_CONVENTION_STATE),
        binding_id=contract.binding_id,
    )
    assert forward.lineage_id.startswith("RESTORE_ISSUED_")
    assert inverse.passed is True
    assert inverse.lineage_id == f"SUPPRESSED_FROM:{forward.lineage_id}"


def test_manual_result_copy_is_rejected_even_with_visible_fields_and_capability() -> None:
    row = _control("ADV_MANUAL_TRANSFORM_RESULT_COPY")
    assert row["changed_premise_count"] == 1
    assert row["expected_first_diagnostic"] == "LINEAGE_PROVENANCE_FAILURE"
    assert row["observed_first_diagnostic"] == "LINEAGE_PROVENANCE_FAILURE"
    assert row["passed"] is True


@pytest.mark.parametrize(
    ("mutation_id", "diagnostic"),
    [
        ("ADV_QUANTUM_OPERATOR_ORDER_REVERSED", "OPERATOR_ORDER_MISMATCH"),
        ("ADV_QUANTUM_DERIVATIVE_SCOPE_CHANGED", "DERIVATIVE_SCOPE_MISMATCH"),
        ("ADV_SUPPRESS_STORED_TARGET_WITHOUT_LINEAGE", "LINEAGE_PROVENANCE_FAILURE"),
        ("ADV_VALID_RESULT_WRONG_BINDING", "LINEAGE_PROVENANCE_FAILURE"),
        ("ADV_WRONG_SI_ORACLE", "EXPECTED_TARGET_MISMATCH"),
        ("ADV_QUANTUM_HBAR_OMITTED", "QUANTUM_HBAR_RESTORATION_MISSING"),
    ],
)
def test_decisive_atomic_controls_produce_exact_diagnostics(
    mutation_id: str,
    diagnostic: str,
) -> None:
    row = _control(mutation_id)
    assert row["changed_premise_count"] == 1
    assert row["expected_first_diagnostic"] == diagnostic
    assert row["observed_first_diagnostic"] == diagnostic
    assert row["passed"] is True


def test_positive_controls_are_separate_from_atomic_negative_controls() -> None:
    packet = _packet()
    positive = packet["production_positive_controls"]
    negative = packet["production_contract_adversarial_controls"]
    assert positive["passed_count"] == positive["required_count"] == 3
    assert all(row["mutation_count"] == 0 for row in positive["rows"])
    assert negative["classification"] == "ATOMIC_SINGLE_PREMISE_NEGATIVE_CONTROLS_ONLY"
    assert negative["passed_count"] == negative["required_count"] == 14
    assert negative["all_single_mutation"] is True
    assert all(row["changed_premise_count"] == 1 for row in negative["rows"])


def test_eight_convention_controls_remain_exact_and_fail_before_output() -> None:
    controls = _packet()["production_convention_negative_controls"]
    assert controls["exact_first_diagnostic_count"] == controls["required_count"] == 8
    assert controls["all_failed_before_output"] is True


def test_v3_authorizes_no_restoration_migration_or_adjacent_lane() -> None:
    scope = _packet()["scope"]
    assert scope == {
        "v3_packet_preparation_only": True,
        "authoritative_equation_restoration_executed": False,
        "scientific_equation_migration_executed": False,
        "authoritative_sources_modified": False,
        "historical_artifacts_modified": False,
        "repository_wide_rewrite_authorized": False,
        "multiple_signatures_or_coordinate_conventions_supported": False,
        "additional_electromagnetic_unit_systems_supported": False,
        "r13_reopened": False,
        "external_comparator_activated": False,
        "automation_created": False,
    }


def test_v3_is_final_automatic_attempt_and_no_v4_is_authorized() -> None:
    stop = _packet()["hard_stop"]
    assert stop["packet_version"] == 3
    assert stop["final_automatically_authorized_implementation_attempt"] is True
    assert stop["automatic_v4_authorized"] is False
    assert stop["v4_requires_fresh_full_project_priority_decision"] is True
    assert stop["successor_if_blocked"] == (
        "CLOSE_LANE_AS_BLOCKED_SR_RESTORATION_TOOLING_CONTRACT"
    )
    assert stop["bounded_restoration_application_authorized_now"] is False
    assert stop["migration_authorized_now"] is False
