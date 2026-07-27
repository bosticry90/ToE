from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    minimal_native_continuum_gravitational_sector_contract_packet_v0 as packet,
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


def test_packet_preserves_every_frozen_authority_and_source_byte() -> None:
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


def test_packet_consumes_selection_and_stops_for_independent_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "INDEPENDENT_MINIMAL_NATIVE_GRAVITATIONAL_CONTRACT_REVIEW_ONLY"
    )


def test_three_provenance_classes_are_exact_and_formula_identity_is_insufficient() -> None:
    provenance = _report()["provenance_contract"]
    assert provenance["class_count"] == len(provenance["classes"]) == 3
    assert provenance["classes"] == packet.PROVENANCE_CLASSES
    assert provenance["exactly_one_initial_class_required"] is True
    assert provenance["formula_identity_determines_provenance"] is False
    assert provenance["renamed_Einstein_Hilbert_is_native"] is False
    assert provenance["project_principle_must_predate_derived_formula"] is True


def test_minimal_field_contract_is_metric_only_and_local() -> None:
    fields = _report()["minimal_field_contract"]
    assert fields["gravitational_field"] == "g_mu_nu"
    assert fields["field_count"] == 1
    assert fields["spacetime_dimension"] == 4
    assert fields["signature"] == "(+,-,-,-)"
    assert fields["coordinate_policy"] == "x^0=ct"
    assert fields["selected_route"] == "LOCAL_METRIC_THEORY"
    assert fields["nonlocal_route_selected"] is False
    assert fields["tetrad_selected"] is False
    assert fields["independent_spin_connection_selected"] is False
    assert fields["full_Dirac_geometry_selected"] is False


def test_symmetry_and_si_dimension_contracts_are_explicit() -> None:
    report = _report()
    symmetry = report["symmetry_contract"]
    assert symmetry["diffeomorphism_covariance_required"] is True
    assert symmetry["locality_required_for_bounded_route"] is True
    assert symmetry["parity_even_baseline"] is True
    assert symmetry["time_reversal_even_baseline"] is True
    assert symmetry["notation_alone_proves_symmetry"] is False
    dimensions = report["dimensional_contract"]
    assert dimensions["target_units"] == "SI"
    assert dimensions["action_dimension"] == "J s"
    assert dimensions["S_over_hbar_dimensionless"] is True
    assert dimensions["manual_equation_specific_restoration_required"] is True
    assert dimensions["automated_SR_restoration_tool_reopened"] is False


def test_boundary_contract_is_local_compact_support_only() -> None:
    boundary = _report()["boundary_variation_contract"]
    assert boundary["claim_scope"] == "LOCAL_BULK_FIELD_EQUATIONS_ONLY"
    assert boundary["region"] == "OPEN_OMEGA_COMPACTLY_CONTAINED_IN_M"
    assert boundary["variation_class"] == (
        "SMOOTH_COMPACTLY_SUPPORTED_METRIC_VARIATIONS"
    )
    assert boundary["global_variational_principle_claimed"] is False
    assert boundary["finite_boundary_claim_authorized"] is False
    assert boundary["boundary_terms_may_be_silently_discarded_elsewhere"] is False


def test_generic_matter_symbol_is_not_mistaken_for_selected_action() -> None:
    matter = _report()["matter_source_contract"]
    assert matter["S_m_g_chi_is_existing_action"] is False
    assert matter["S_m_g_chi_status"] == "CONTRACT_NOTATION_ONLY"
    assert matter["matter_field_content_selected_in_current_authority"] is False
    assert matter["matter_lagrangian_selected_in_current_authority"] is False
    assert matter["retained_stress_policies_are_oracles_only"] is True
    assert matter["inserting_retained_stress_as_input_allowed"] is False
    assert matter["T_0i_representability_required"] is True


def test_ck_firewall_and_existing_object_nontransport_are_exact() -> None:
    report = _report()
    firewall = report["C_k_firewall"]
    assert firewall["classification"] == "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY"
    assert firewall["action_embedding_allowed"] is False
    assert firewall["variation_allowed"] is False
    assert firewall["multiplier_allowed"] is False
    assert firewall["quadratic_penalty_allowed"] is False
    assert firewall["historical_v0_modified"] is False
    objects = report["existing_object_boundaries"]
    assert objects["historical_master_action_v0"] == (
        "SCHEMATIC_SECTOR_INVENTORY_ONLY"
    )
    assert objects["Rep32"] == "SEPARATE_STRUCTURAL_MODEL_NO_CONTINUUM_TRANSPORT"
    assert objects["Einstein_scalar_sandbox"] == (
        "SUPPLIED_PROVISIONAL_COMPARATOR_ONLY"
    )
    assert objects["authority_flows_automatically"] is False


def test_twelve_completeness_gates_are_frozen_before_variation() -> None:
    contract = _report()["candidate_completeness_contract"]
    assert contract["gate_count"] == len(contract["gates"]) == 12
    assert contract["gates"] == packet.CANDIDATE_COMPLETENESS_GATES
    assert contract["undefined_correction_fails_before_variation"] is True
    assert len(contract["nonstandard_term_required_fields"]) == 7


def test_ten_stage_recovery_ladder_is_frozen_and_unexecuted() -> None:
    recovery = _report()["recovery_contract"]
    assert recovery["stage_count"] == len(recovery["stages"]) == 10
    assert recovery["stages"] == packet.RECOVERY_LADDER
    assert recovery["executed_stage_count"] == 0
    assert recovery["earlier_failure_blocks_later_stages"] is True


def test_six_outcomes_include_fail_closed_and_no_go_redirects() -> None:
    outcomes = _report()["outcome_contract"]
    assert outcomes["outcome_count"] == len(outcomes["allowed_outcomes"]) == 6
    assert outcomes["allowed_outcomes"] == packet.ALLOWED_OUTCOMES
    assert outcomes["exactly_one_required"] is True
    assert outcomes["selection_base_outcome_count"] == 4
    assert outcomes["fail_closed_refinement_count"] == 2


def test_eight_review_controls_are_atomic_and_not_preexecuted() -> None:
    controls = _report()["control_contract"]
    assert controls["control_count"] == len(controls["rows"]) == 8
    assert controls["rows"] == packet.ATOMIC_CONTROLS
    assert controls["all_single_mutation"] is True
    assert all(row["mutation_count"] == 1 for row in controls["rows"])
    assert controls["controls_executed_by_preparation"] is False
    assert controls["independent_review_execution_required"] is True


def test_packet_creates_no_action_variation_gr_result_tooling_or_automation() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_only"] is True
    for key, value in scope.items():
        if key != "packet_preparation_only":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No gravitational action",
        "successor master action",
        "variation",
        "tensor field equation",
        "tooling lane",
        "automation",
    ):
        assert token in claim
