from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_gauge_and_auxiliary_constraint_propagation_system
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_gauge_and_auxiliary_constraint_propagation_system_result_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_calculation_and_review_artifacts_are_current() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_off_constraint_extension_is_exactly_the_accepted_system() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    extension = artifact["off_constraint_extension"]
    assert extension["frozen_equations"] == [
        "E_g^H",
        "E_R",
        "E_r",
        "E_c",
        "E_S",
    ]
    assert extension["constraint_addition_M_A_B"] == "identically zero"
    assert (
        extension["derivative_constraint_addition_N_A_B_mu"]
        == "identically zero"
    )
    assert extension["constraint_damping"] == "none"
    assert extension["changes_physical_spin2_block"] is False
    assert extension["regularizer_or_fiducial_mode_added"] is False


def test_defect_operators_include_metric_definition_violations() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    operators = artifact["exact_defect_operators"]
    assert "R_mn[g]-R^H_mn[g,c,H]" in operators["total_ricci_defect"]
    assert "K_tot_mn-K_H_mn" in operators[
        "metric_definition_ricci_defect"
    ]
    assert "V_tot=V_H+V_c" in operators["divergence_defects"]
    assert "operator equality" in operators["no_implicit_remainder"]
    assert "lower(" not in str(artifact)
    assert "..." not in str(artifact)


def test_definition_and_integrability_hierarchy_is_finite() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    identities = artifact["exact_propagation_identities"]
    assert identities["scalar_derivative_definition"]["equation"] == (
        "W_g C_r_a = -(partial_a g^bc)partial_b C_r_c"
    )
    assert identities["metric_derivative_definition"]["equation"] == (
        "W_g C_c_mna = -(partial_a g^bc)partial_b C_c_mnc"
    )
    assert identities["scalar_integrability"]["identity"] == (
        "I_R_ab=partial_a C_r_b-partial_b C_r_a"
    )
    assert identities["metric_integrability"]["identity"] == (
        "I_g_mnab=partial_a C_c_mnb-partial_b C_c_mna"
    )
    system = artifact["finite_subsidiary_system"]
    assert system["new_constraint_generated_by_differentiation"] is False
    assert system["finite"] is True
    assert system["homogeneous"] is True
    assert system["P_C_of_zero"] == "0"


def test_trace_bianchi_and_curvature_definitions_reconstruct() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    identities = artifact["exact_propagation_identities"]
    assert identities["trace"]["equation"] == (
        "beta Box_g T+[c_R+(2alpha+beta)R]T"
        "+2beta K_tot_mn S^mn=0"
    )
    assert identities["contracted_bianchi"]["equation"] == (
        "V_tot_n=-D_n-(1/2)C_r_n+(1/2)nabla_n T"
    )
    assert identities["scalar_curvature_definition"]["equation"] == (
        "C_R=-(T+K_tot)"
    )
    assert identities["tracefree_ricci_definition"]["equation"] == (
        "C_S_mn=-K_tot_mn+(1/4)g_mn(T+K_tot)"
    )
    assert all(row["homogeneous"] is True for row in identities.values())


def test_independent_subsidiary_pencil_has_complete_lightcone_basis() -> None:
    direct = calculation.derive_subsidiary_pencil()
    assert direct["unit_wave_components"] == 64
    assert direct["beta_wave_components"] == 5
    assert direct["independent_wave_components"] == 69
    assert direct["determinant"] == (
        "-beta**5*(lambda - 1)**69*(lambda + 1)**69"
    )
    assert direct["roots"] == [-1, 1]
    assert direct["algebraic_multiplicity_each_root"] == 69
    assert direct["geometric_multiplicity_each_root"] == 69
    assert direct["complete_eigenbasis"] is True
    assert direct["strongly_hyperbolic"] is True


def test_constraint_classification_does_not_overprescribe_data() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    rows = {
        row["id"]: row for row in artifact["constraint_classification"]
    }
    assert rows["C_H^a"]["classification"] == (
        "INDEPENDENT_INITIAL_CONSTRAINT"
    )
    assert rows["Phi^a_b"]["classification"] == "DEFINITION_CONSTRAINT"
    assert rows["I_R_ab"]["classification"] == (
        "INTEGRABILITY_CONSEQUENCE"
    )
    assert rows["D_n"]["classification"] == "EVOLUTION_CONSEQUENCE"
    assert rows["normal_derivative_of_V_H"]["classification"] == (
        "REDUNDANT_BY_BIANCHI_IDENTITY"
    )


def test_hamiltonian_momentum_propagation_is_noncircular() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    propagation = artifact["hamiltonian_momentum_propagation"]
    assert "E_mn=0 is not assumed" in propagation["noncircular"]
    assert "nabla^m[" in propagation["exact_normal_projection_identity"]
    assert "nabla^m[" in propagation[
        "exact_tangential_projection_identity"
    ]
    assert propagation["conclusion"].startswith(
        "zero Hamiltonian/momentum data propagate"
    )


def test_derivative_loss_is_bounded_without_energy_theorem() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    regularity = artifact["regularity_conclusion"]
    assert regularity["candidate_integer_s"] == (
        "s >= 3 in three spatial dimensions"
    )
    assert regularity["fixed_loss"] == 1
    assert regularity["optimality_proved"] is False
    assert regularity["loss_accumulation_analyzed"] is False
    assert regularity["energy_estimate_for_full_reduced_system"] is False
    assert regularity["local_existence_theorem"] is False


def test_review_accepts_only_full_reduced_principal_structure_next() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    rotation = artifact["authority_rotation"]
    assert rotation["constraint_propagation_result_accepted"] is True
    assert rotation["full_reduced_principal_structure_authorized"] is True
    assert rotation["adapted_energy_estimate_authorized"] is False
    assert rotation["local_existence_theorem_authorized"] is False
    assert rotation["source_extension_authorized"] is False
    assert "ORDINARY_METRIC_STRONG_HYPERBOLICITY" in artifact[
        "not_established"
    ]
    assert all(review.build_review()["checks"].values())
