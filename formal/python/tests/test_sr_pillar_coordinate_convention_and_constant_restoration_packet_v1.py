from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v1 as packet_v1,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet_v1.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _packet() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    first = packet_v1.artifact_bytes()
    second = packet_v1.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_build_preserves_all_bound_authority_and_equation_sources() -> None:
    before = {
        path: _sha256(REPO_ROOT / path) for path in packet_v1.SOURCE_HASHES
    }
    packet_v1.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path) for path in packet_v1.SOURCE_HASHES
    }
    assert before == after == packet_v1.SOURCE_HASHES


def test_v1_consumes_exact_blocked_review_and_stops_at_independent_review() -> None:
    packet = _packet()
    assert packet["target"] == packet_v1.TARGET
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == packet_v1.SELECTED_NEXT_TARGET
    assert packet["authority"]["consumed_v0_review_verdict"] == (
        "BLOCKED_INCOMPLETE_ELECTROMAGNETIC_QUANTUM_CONVENTION_CLOSURE"
    )


def test_coordinate_index_and_derivative_lock_is_single_and_complete() -> None:
    lock = _packet()["coordinate_index_and_derivative_lock"]
    assert lock["coordinate_definition"] == "x^mu=(c t,x,y,z)"
    assert lock["metric_signature"] == "(+,-,-,-)"
    assert lock["partial_mu"].startswith("(c^-1 partial_t")
    assert lock["p^mu"] == "(E/c,p_vector)"
    assert lock["J_SI^mu"] == "(c rho,j_vector)"


def test_electromagnetic_tensor_components_lowering_and_dual_are_closed() -> None:
    em = _packet()["electromagnetic_tensor_closure"]
    assert em["upper_components"] == (
        "F^{0i}=-E^i/c; F^{i0}=+E^i/c; F^{ij}=-epsilon_3^{ijk} B_k"
    )
    assert em["four_dimensional_orientation"].startswith("varepsilon^{0123}=+1")
    assert em["dual_components"] == (
        "starF^{0i}=-B^i; starF^{ij}=+epsilon_3^{ijk} E_k/c"
    )
    audit = em["executable_tensor_audit"]
    assert audit["antisymmetry_passed"] is True
    assert audit["metric_lowering_passed"] is True
    assert audit["dual_component_audit_passed"] is True
    assert audit["passed"] is True


def test_si_maxwell_component_equations_match_the_frozen_tensor_signs() -> None:
    em = _packet()["electromagnetic_tensor_closure"]
    assert "div E=rho/epsilon_0" in em["sourced_maxwell_SI"]
    assert "curl B-c^-2 partial_t E=mu_0 j" in em["sourced_maxwell_SI"]
    assert em["vacuum_identity"] == "mu_0 epsilon_0 c^2=1"
    assert "curl E+partial_t B=0" in em["homogeneous_maxwell"]


def test_quantum_hbar_normalization_closes_derivative_phase_and_source_current() -> None:
    quantum = _packet()["quantum_hbar_normalization"]
    assert quantum["signed_charge_policy"] == "q_SI is the signed electric charge of psi"
    assert quantum["coefficient_identity"] == "q_star A_star = q_SI A_SI/hbar"
    assert quantum["phase_identity"] == "q_star chi_star=q_SI chi_SI/hbar"
    assert "J_SI=q_SI c psibar" in quantum["current_identity"]
    assert quantum["forward_passed"] is True
    assert quantum["reverse_passed"] is True
    assert quantum["passed"] is True


def test_stress_energy_dictionary_fixes_all_component_meanings_and_symmetry_scope() -> None:
    stress = _packet()["stress_energy_component_dictionary"]
    assert stress["T^00"] == "energy density"
    assert stress["T^0i"] == "energy flux^i/c=c times momentum density^i"
    assert "equals T^0i only under" in stress["T^i0"]
    assert "momentum-flux tensor" in stress["T^ij"]
    assert "arbitrary canonical tensor" in stress["symmetry_assumption"]
    assert stress["component_dimension"] == "[T^{mu nu}]=J m^-3=Pa for every component under x^0=ct"


def test_flat_curved_adapter_is_explicit_but_does_not_derive_tetrad_gravity() -> None:
    adapter = _packet()["flat_curved_derivative_adapter"]
    assert adapter["curved_scalar"] == "nabla_mu phi=partial_mu phi"
    assert "Gamma" in adapter["curved_vector"]
    assert adapter["curved_spinor"] == "nabla_spin_mu psi=partial_mu psi+Omega_mu psi"
    assert "+i q_SI A_mu psi/hbar" in adapter["gauge_plus_spin"]
    assert "not derived" in adapter["bounded_nonclaim"]
    assert "Gamma=Omega=0" in adapter["source_adapter"]


def test_all_six_exact_project_source_bindings_validate() -> None:
    bindings = _packet()["source_bindings"]
    assert bindings["required_count"] == 6
    assert bindings["validated_count"] == 6
    rows = bindings["rows"]
    assert [row["equation_id"] for row in rows] == list(packet_v1.EQUATION_CONTRACTS)
    assert all(row["binding_validated"] for row in rows)
    assert all(len(row["artifact_sha256"]) == 64 for row in rows)
    mass = next(row for row in rows if row["equation_id"] == "SR_MASS_SHELL")
    assert mass["locator"] == "_make_report: omega2 assignment"
    assert mass["corroborating_value"] == "RL/dispersion_front_door_report/v1"


def test_all_six_bidirectional_canonical_round_trips_pass() -> None:
    trips = _packet()["bidirectional_round_trips"]
    assert trips["required_count"] == 6
    assert trips["passed_count"] == 6
    assert len(trips["rows"]) == 6
    assert all(row["forward_passed"] and row["reverse_passed"] for row in trips["rows"])
    assert all(row["passed"] for row in trips["rows"])


def test_round_trip_functions_reject_conventionally_inequivalent_asts() -> None:
    source = packet_v1.EQUATION_CONTRACTS["SOURCED_MAXWELL"]["natural_ast"]
    assert isinstance(source, tuple)
    mutated = ("eq", ("divergence", "nabla_mu", "F_N^{mu nu}"), ("mul", "mu_0", "J_N^nu"))
    with pytest.raises(ValueError, match="NATURAL_CANONICAL_SOURCE_MISMATCH"):
        packet_v1.restore_equation("SOURCED_MAXWELL", mutated)
    target = packet_v1.EQUATION_CONTRACTS["SOURCED_MAXWELL"]["si_ast"]
    assert isinstance(target, tuple)
    wrong_sign = ("eq", target[1], ("neg", target[2]))
    with pytest.raises(ValueError, match="SI_CANONICAL_TARGET_MISMATCH"):
        packet_v1.suppress_equation("SOURCED_MAXWELL", wrong_sign)


def test_eight_negative_controls_execute_with_exact_first_diagnostics() -> None:
    controls = _packet()["executable_negative_controls"]
    assert controls["base_state_first_diagnostic"] == "PASS"
    assert controls["required_count"] == 8
    assert controls["exact_first_diagnostic_count"] == 8
    assert len(controls["rows"]) == 8
    assert all(row["changed_field_count"] == 1 for row in controls["rows"])
    assert all(
        row["expected_first_diagnostic"] == row["observed_first_diagnostic"]
        for row in controls["rows"]
    )


def test_negative_control_order_reports_the_first_defect_only() -> None:
    state = dict(packet_v1.BASE_CONVENTION_STATE)
    state["partial_0"] = "partial_t"
    state["F^{0i}"] = "+E^i/c"
    assert packet_v1.first_diagnostic(state) == "PARTIAL0_MISSING_C_INVERSE"


def test_scope_blocks_application_migration_r13_and_automation() -> None:
    scope = _packet()["scope"]
    assert scope["convention_closure_packet_only"] is True
    assert scope["authoritative_equation_restoration_executed"] is False
    assert scope["scientific_equation_migration_executed"] is False
    assert scope["historical_artifacts_modified"] is False
    assert scope["repository_wide_rewrite_authorized"] is False
    assert scope["general_purpose_units_engine_built"] is False
    assert scope["curved_spinor_geometry_derived"] is False
    assert scope["r13_reopened"] is False
    assert scope["external_comparator_activated"] is False
    assert scope["automation_created"] is False


def test_hard_stop_requires_independent_review_before_any_application() -> None:
    packet = _packet()
    hard_stop = packet["hard_stop"]
    assert hard_stop["independent_packet_review_required"] is True
    assert hard_stop["equation_restoration_application_authorized_now"] is False
    assert hard_stop["migration_authorized_now"] is False
    assert hard_stop["repository_wide_rewrite_authorized"] is False
    assert "no SR recovery" in packet["claim_ceiling"]
