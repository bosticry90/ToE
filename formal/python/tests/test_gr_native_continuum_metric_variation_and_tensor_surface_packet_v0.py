from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    gr_native_continuum_metric_variation_and_tensor_surface_packet_v0 as packet,
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


def test_packet_consumes_selected_target_and_stops_for_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == "INDEPENDENT_PACKET_REVIEW_ONLY"
    assert report["hard_stop"]["only_independent_packet_review_next"] is True
    assert report["hard_stop"]["variation_authorized_now"] is False


def test_exactly_one_native_candidate_is_bound_without_surface_blending() -> None:
    source = _report()["sole_action_candidate"]
    assert source == {
        "source_id": "TOE_CANDIDATE_MASTER_ACTION_v0",
        "relative_path": "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md",
        "source_classification": "TOE_NATIVE_CANDIDATE",
        "current_authority": "WORKING_FORM_NONCANONICAL_UNPROMOTED",
        "variational_readiness": "UNADJUDICATED_PENDING_INDEPENDENT_REVIEW",
        "byte_exact_source_required": True,
        "term_insertion_removal_or_reclassification_allowed": False,
        "source_blending_allowed": False,
    }
    excluded = _report()["excluded_or_comparator_surfaces"]
    assert excluded["required_count"] == len(excluded["rows"]) == 5


def test_full_candidate_selects_tetrad_gate_without_claiming_it_is_complete() -> None:
    variable = _report()["gravitational_variable_contract"]
    assert variable["full_candidate_variable"] == "covariant tetrad e^a_mu"
    assert variable["formulation"] == "SECOND_ORDER_TORSION_FREE_TETRAD"
    assert len(variable["required_structures"]) == 7
    assert variable["metric_symbol_only_full_candidate_variation_allowed"] is False
    assert variable["route_authorized_as_complete_before_review"] is False
    assert variable["missing_contract_diagnostic"] == (
        "BLOCKED_SPINOR_METRIC_VARIATION_SURFACE"
    )


def test_domain_and_units_gate_forbids_silent_constant_restoration() -> None:
    gate = _report()["continuum_domain_and_units_gate"]
    assert gate["retained_signature"] == "(+,-,-,-)"
    assert gate["retained_temporal_coordinate"] == "x^0=c t"
    assert gate["dimensionful_target"] == "SI"
    assert gate["source_unit_posture"] == (
        "NATURAL_UNIT_LIKE_SHORTHAND_NOT_EXPLICITLY_CLOSED"
    )
    assert gate["constant_insertion_or_field_rescaling_during_review_allowed"] is False


def test_complete_six_sector_dependency_ledger_is_required() -> None:
    ledger = _report()["metric_dependency_ledger"]
    assert ledger["required_count"] == len(ledger["rows"]) == 6
    assert {row["sector"] for row in ledger["rows"]} == {
        "geometry", "Dirac", "gauge", "scalar", "statistical", "C_k"
    }
    assert ledger["hidden_dependency_allowed"] is False
    assert ledger["stress_tensor_substitution_for_missing_dependency_allowed"] is False


def test_boundary_contract_is_local_compact_support_only() -> None:
    boundary = _report()["boundary_contract"]
    assert boundary["selected_route"] == "LOCAL_BULK_COMPACT_SUPPORT"
    assert boundary["variation"] == "delta e^a_mu in C_c^infinity(interior(M))"
    assert boundary["GHY_term_added"] is False
    assert boundary["finite_boundary_variational_principle_claimed"] is False
    assert boundary["silent_boundary_term_discard_allowed"] is False


def test_stress_energy_must_be_variation_generated_not_policy_inserted() -> None:
    source = _report()["matter_source_contract"]
    assert source["metric_subroute_definition"] == (
        "T_mu_nu=-(2/sqrt(-g)) delta S_m/delta g^mu_nu"
    )
    assert source["selected_tetrad_definition"] == (
        "tau_a^mu=(1/e) delta S_m/delta e^a_mu"
    )
    assert source["retained_T_A_T_psi_T_total_classification"] == (
        "COMPARISON_POLICIES_NOT_VARIATION_DERIVED"
    )
    assert source["previous_stress_tensor_may_replace_variation"] is False


def test_ck_firewall_records_source_conflict_without_rewriting_action() -> None:
    firewall = _report()["C_k_firewall"]
    assert firewall["retained_policy"] == "ADMISSIBILITY_AUDIT_ONLY"
    assert firewall["action_embedding_authorized"] is False
    assert firewall["variation_authorized"] is False
    assert firewall["selected_source_contains_displayed_C_k_multiplier_term"] is True
    assert firewall["preparation_finding"] == "REGISTERED_SOURCE_POLICY_CONFLICT"
    assert firewall["packet_rewrites_action"] is False
    assert firewall["required_review_diagnostic_if_unresolved"] == (
        "CK_FIREWALL_ACTION_SOURCE_CONFLICT"
    )


def test_rep32_remains_separate_structural_model() -> None:
    relation = _report()["Rep32_relationship"]
    assert relation["classification"] == (
        "SEPARATE_STRUCTURAL_MODEL_CONTINUUM_RELATION_UNESTABLISHED"
    )
    assert relation["discretization_theorem_available"] is False
    assert relation["reduction_theorem_available"] is False
    assert relation["convergence_theorem_available"] is False
    assert relation["analytic_first_variation_from_actionRep32_available"] is False
    assert relation["prior_transport_result"] == (
        "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
    )


def test_review_is_fail_fast_with_five_exact_terminal_outcomes() -> None:
    protocol = _report()["independent_review_protocol"]
    assert protocol["fail_fast"] is True
    assert protocol["diagnostics_in_order"] == packet.FAIL_FAST_DIAGNOSTICS
    assert len(protocol["diagnostics_in_order"]) == 11
    assert protocol["allowed_outcomes"] == packet.ALLOWED_OUTCOMES
    assert len(protocol["allowed_outcomes"]) == 5
    assert protocol["exactly_one_terminal_outcome_required"] is True
    assert protocol["passing_later_gate_repairs_earlier_failure"] is False


def test_packet_executes_no_variation_comparator_or_promotion() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_only"] is True
    for key, value in scope.items():
        if key != "packet_preparation_only":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No continuum tensor field surface",
        "Einstein equation",
        "GR recovery",
        "master-action promotion",
        "automation",
    ):
        assert token in claim
