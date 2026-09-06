from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0 as packet,
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
    first = packet.artifact_bytes()
    second = packet.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


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


def test_packet_consumes_selected_gr_target_and_stops_for_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == "INDEPENDENT_PACKET_REVIEW_ONLY"
    assert report["hard_stop"]["only_independent_packet_review_next"] is True
    assert report["hard_stop"]["bounded_derivation_authorized_now"] is False


def test_exact_project_surfaces_are_bound_without_importing_einstein_equation() -> None:
    bindings = _report()["project_source_bindings"]
    assert bindings["required_count"] == len(bindings["rows"]) == 3
    ids = {row["binding_id"] for row in bindings["rows"]}
    assert ids == {
        "GR_PROJECT_ACTION_REP32_SCAFFOLD",
        "GR_PROJECT_BOUNDED_DISCRETE_WEAK_FIELD_POISSON",
        "GR_PROJECT_DISCHARGE_BOUNDARY",
    }
    assert bindings["first_registered_failure"] == "FIELD_EQUATION_SURFACE_FAILURE"
    assert "cannot be substituted" in bindings["starting_surface_rule"]


def test_retained_coordinate_signature_and_si_policy_are_exact() -> None:
    convention = _report()["retained_convention"]
    assert convention == {
        "temporal_coordinate": "x^0=c t",
        "background_metric": "eta_mu_nu=diag(+1,-1,-1,-1)",
        "dimensionful_target": "SI",
        "metric_perturbation": "g_mu_nu=eta_mu_nu+h_mu_nu; |h_mu_nu|<<1",
        "spatial_component_policy": "Euclidean three-vector labels for i,j,k",
        "sr_tooling_reopened": False,
        "equation_specific_derivation_required": True,
    }


def test_regime_and_current_dipole_source_contract_are_closed() -> None:
    report = _report()
    regime = report["regime_and_ordering"]
    assert regime["stationary_source"] == "partial_0 T_mu_nu=0 at retained order"
    assert regime["retained_source_conservation"] == (
        "partial_mu T^{mu nu}=0 at retained order"
    )
    assert regime["exterior_domain"] == "r>R_s"
    assert regime["weak_field_order"] == "linear in h_mu_nu"
    assert regime["rotation_order"] == "linear in J"
    assert len(regime["retained_multipoles"]) == 2
    assert len(regime["discarded_terms"]) == 6
    source = report["source_contract"]
    assert source["contravariant_mixed_component"] == "T^{0i}=c j_m^i+higher order"
    assert source["covariant_mixed_component"] == "T_0i=-c j_m_i+higher order"
    assert source["mass_center_condition"] == "integral rho_m x d^3x=0"
    assert source["zero_total_momentum_condition"] == "integral j_m d^3x=0"
    assert source["angular_momentum"] == "J=integral x cross j_m(x) d^3x"
    assert source["current_moment_identity_to_derive"] == (
        "integral j_m_i x'_j d^3x'=-(1/2)epsilon_ijk J_k"
    )
    assert "harmonic-gauge compatibility" in source["conservation_policy"]


def test_trace_reversal_harmonic_gauge_residual_and_boundaries_are_frozen() -> None:
    gauge = _report()["gauge_and_boundary_contract"]
    assert gauge["trace_reversal"] == "hbar_mu_nu=h_mu_nu-(1/2)eta_mu_nu h"
    assert gauge["gauge"] == "partial^mu hbar_mu_nu=0"
    assert gauge["residual_gauge_equation"] == (
        "box xi_mu=0; stationary: nabla^2 xi_mu=0"
    )
    assert "asymptotically decaying" in gauge["residual_gauge_boundary"]
    assert gauge["mixed_component_identity"] == "hbar_0i=h_0i=g_0i at linear order"
    assert gauge["green_normalization"] == (
        "nabla^2(1/|x-x'|)=-4 pi delta^3(x-x')"
    )
    assert len(gauge["boundaries"]) == 3


def test_standard_gr_values_are_isolated_comparison_oracles_only() -> None:
    report = _report()
    oracle = report["independent_recovery_oracles"]
    assert oracle["classification"] == (
        "INDEPENDENT_RECOVERY_ORACLE_NOT_DERIVATION_INPUT"
    )
    assert oracle["visibility_rule"] == (
        "COMPARE_ONLY_AFTER_COMPUTED_RESULT_AND_PROVENANCE_ARE_FROZEN"
    )
    assert oracle["stationary_0i_equation"] == (
        "nabla^2 hbar_0i=+(16 pi G/c^4)T_0i"
    )
    assert oracle["exterior_rotational_metric"] == (
        "g_0i^rot=+(2G/c^3)(J cross r)_i/r^3"
    )
    assert oracle["nodal_rate"] == (
        "dot(Omega)_LT=+(2GJ)/(c^2 a^3 (1-e^2)^(3/2))"
    )
    assert oracle["oracle_used_as_input"] is False
    forbidden = report["derivation_inputs"]["forbidden"]
    assert "metric coefficient oracle" in forbidden
    assert "nodal coefficient oracle" in forbidden


def test_route_is_analytic_source_to_field_to_orbit_and_oracle_last() -> None:
    route = _report()["authorized_future_derivation_route"]
    assert route["stage_count"] == len(route["stages"]) == 7
    assert route["stages"][0].startswith("derive or justify a continuum tensor")
    assert "emit and freeze" in route["stages"][4]
    assert "compare frozen" in route["stages"][6]
    assert route["orbit_average_identity_to_derive_or_independently_check"] == (
        "<r^-3>=a^-3(1-e^2)^(-3/2)"
    )
    assert route["numerical_orbit_integration_authorized"] is False


def test_eight_controls_are_atomic_and_cover_decisive_failures() -> None:
    controls = _report()["required_controls"]
    assert controls["required_count"] == len(controls["rows"]) == 8
    assert controls["all_atomic_single_premise"] is True
    assert all(row["changed_premise_count"] == 1 for row in controls["rows"])
    ids = {row["control_id"] for row in controls["rows"]}
    assert ids == {
        "ZERO_ANGULAR_MOMENTUM",
        "ANGULAR_MOMENTUM_SIGN_REVERSAL",
        "WRONG_SOURCE_COMPONENT",
        "MIXED_METRIC_COMPONENT_REMOVAL",
        "WRONG_GREEN_NORMALIZATION",
        "SIGNATURE_MIX",
        "COEFFICIENT_FIT_ATTEMPT",
        "NONDECAYING_EXTERIOR_MODE",
    }


def test_success_ceiling_and_six_failure_classes_are_exact() -> None:
    result = _report()["result_classification"]
    assert result["maximum_success"] == (
        "BOUNDED_GR_ROTATING_WEAK_FIELD_RECOVERY_CANDIDATE_PENDING_RESULT_REVIEW"
    )
    assert result["failure_classes"] == packet.FAILURE_CLASSES
    assert len(result["failure_classes"]) == 6
    assert result["failure_is_scientifically_usable"] is True
    assert result["success_accepted_without_separate_result_review"] is False


def test_benchmark_is_reference_only_without_data_or_fit_activation() -> None:
    posture = _report()["benchmark_posture"]
    assert posture == {
        "benchmark_id": "GR-WEAK-ROTATING-SOURCE-BENCHMARK",
        "status": "REFERENCE_BOUND_FOR_SELECTED_GR_PREPARATION_ONLY",
        "LARES_2_data_analysis_authorized": False,
        "empirical_fit_authorized": False,
        "modified_gravity_constraint_claim_authorized": False,
    }


def test_packet_executes_no_derivation_tooling_migration_or_automation() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_only"] is True
    for key, value in scope.items():
        if key != "packet_preparation_only":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No gravitomagnetic or Lense-Thirring derivation",
        "GR-pillar completion",
        "seam closure",
        "master-action promotion",
    ):
        assert token in claim
