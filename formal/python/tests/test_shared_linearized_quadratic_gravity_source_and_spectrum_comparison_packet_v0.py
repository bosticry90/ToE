from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_consumes_review_authority() -> None:
    assert packet.artifact_bytes() == packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["authority"]["consumed_result_review_verdict"].startswith(
        "ACCEPTED_AUTHORIZE_SHARED_LINEARIZED"
    )
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_result_review_artifacts"]
    } == packet.RESULT_REVIEW_HASHES


def test_comparison_only_classification_is_exact() -> None:
    classification = _report()["classification"]
    assert tuple(classification["binding_labels"]) == packet.COMPARISON_STATUS_LABELS
    assert classification["status"] == "SUPPLIED_COMPARISON_FAMILY"
    assert classification["ToE_adoption"] == "NONE"
    assert classification["native_principle"] == "NONE"
    assert classification["candidate_action_authority"] == "NONE"
    assert classification["successful_calculation_promotes_action"] is False


def test_action_uses_one_common_normalization_and_SI_dimensions() -> None:
    action = _report()["comparison_action_contract"]
    assert action["A_EH"] == "c^3/(16 pi G)"
    assert action["kappa"] == "8 pi G/c^4"
    assert action["action"] == (
        "S_g^cmp=A_EH integral d^4x sqrt(-g)"
        "[R+alpha R^2+beta R_mu_nu R^mu_nu]"
    )
    assert action["alpha_dimension_SI"] == "m^2"
    assert action["beta_dimension_SI"] == "m^2"
    assert action["action_dimension_SI"] == "J s"
    assert action["alpha_beta_domain"] == "symbolic real parameters"
    assert action["alpha_beta_are_project_parameters"] is False
    assert action["alpha_beta_perturbative"] is False
    assert action["coefficient_fitting_authorized"] is False


def test_external_source_is_normalized_but_not_a_matter_action() -> None:
    source = _report()["external_source_contract"]
    assert source["source_status"] == (
        "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE"
    )
    assert source["symmetry"] == "T_mu_nu=T_nu_mu"
    assert source["conservation"] == "partial_mu T^mu_nu = 0"
    assert source["first_variation"].startswith("delta S_ext|eta=-(1/(2c))")
    assert source["linear_coupling"].startswith("S_ext^(1)=+(1/(2c))")
    assert source["required_derived_equation_normalization"] == (
        "E_mu_nu^lin=kappa T_mu_nu"
    )
    assert source["mass_density_probe_definition"] == "rho=T_00/c^2"
    assert source["ToE_matter_action_selected"] is False
    assert source["variation_derived_ToE_stress_energy"] is False
    assert source["matter_field_content_selected"] is False


def test_gauss_bonnet_reduction_is_exactly_four_dimensional_local_bulk() -> None:
    basis = _report()["quadratic_basis_contract"]
    assert basis["dimension"] == 4
    assert basis["unreduced_basis"] == [
        "R^2",
        "R_mu_nu R^mu_nu",
        "R_mu_nu_rho_sigma R^mu_nu_rho_sigma",
    ]
    assert basis["Euler_density"] == "E_4=Riemann^2-4 Ricci^2+R^2"
    assert basis["coefficient_map"] == {
        "alpha_reduced": "alpha_unreduced-gamma",
        "beta_reduced": "beta_unreduced+4 gamma",
    }
    assert basis["local_bulk_reduction_only"] is True
    assert basis["boundary_global_transport_allowed"] is False
    for token in ("boundary charges", "global topology", "D!=4", "nonlocal theories"):
        assert token in basis["nonclaims"]


def test_geometry_order_and_curvature_conventions_are_frozen() -> None:
    geometry = _report()["geometry_and_order_contract"]
    assert geometry["coordinate_time"] == "x^0=c t"
    assert geometry["metric_signature"] == "(+,-,-,-)"
    assert geometry["background_metric"] == "eta_mu_nu=diag(+1,-1,-1,-1)"
    assert geometry["perturbation"] == "g_mu_nu=eta_mu_nu+h_mu_nu"
    assert geometry["Ricci_convention"] == "R_sigma_nu=R^rho_sigma_rho_nu"
    assert geometry["Box"].startswith("eta^mu_nu partial_mu partial_nu")
    assert geometry["gravitational_action_expansion"] == "through O(h^2)"
    assert geometry["field_equation_order"] == "through O(h)"
    assert geometry["alpha_beta_perturbative"] is False
    assert geometry["Minkowski_background_must_be_verified"] is True


def test_fourier_gauge_and_green_prescriptions_are_disjoint() -> None:
    analytic = _report()["fourier_gauge_and_green_contract"]
    assert analytic["fourier_kernel"] == (
        "exp[-i k_mu x^mu] = exp[i(k_vec.x_vec-omega t)]"
    )
    assert analytic["partial_symbol"] == "-i k_mu"
    assert analytic["Box_symbol"] == "-k^2"
    assert analytic["gauge"] == "de Donder F_nu=0 with xi=1"
    assert analytic["classical_dynamic_prescription"] == "RETARDED"
    assert analytic["residue_reporting_label"] == (
        "FEYNMAN +i0 FOR POLE ORIENTATION ONLY"
    )
    assert analytic["stationary_spatial_prescription"] == "DECAY_AT_INFINITY"
    assert analytic["growing_Yukawa_branch_allowed"] is False
    assert analytic["prescriptions_may_be_conflated"] is False


def test_projector_contract_requires_complete_inversion_and_saturation() -> None:
    projectors = _report()["projector_contract"]
    assert projectors["theta"].startswith("theta_mu_nu=")
    assert projectors["P2"].startswith("P2=")
    assert projectors["P0s"].startswith("P0s=")
    assert projectors["complete_longitudinal_projectors_required_for_inversion"] is True
    assert projectors["conserved_source_saturation_required"] is True
    assert projectors["massless_pole_interpretation"] == (
        "conserved-source saturated limit"
    )
    assert projectors["standalone_singular_theta_is_observable"] is False
    assert projectors["gauge_independence_check_required"] is True


def test_ten_step_derivation_plan_is_prepared_but_unexecuted() -> None:
    plan = _report()["derivation_plan"]
    assert plan["step_count"] == 10
    assert plan["executed_step_count"] == 0
    assert [row["order"] for row in plan["rows"]] == list(range(1, 11))
    assert all(row["status"] == "NOT_EXECUTED" for row in plan["rows"])
    assert all(row["derived_output"] is None for row in plan["rows"])
    assert plan["literature_oracle_allowed_only_after_derivation"] is True


def test_mode_register_has_zero_scientific_judgments() -> None:
    register = _report()["mode_pole_residue_register"]
    assert register["sector_count"] == 3
    assert register["scientific_judgment_count"] == 0
    for row in register["rows"]:
        for field in (
            "presence", "pole", "mass_squared", "residue_sign",
            "tachyon_condition", "coupled_source_component",
        ):
            assert row[field] == "TO_BE_DERIVED"
        assert row["scientific_judgment_made"] is False
    assert set(register["required_distinctions"]) == {
        "GHOST", "TACHYON", "CLASSICAL_INSTABILITY",
        "MATTER_INSTABILITY", "HEAVY_DECOUPLED_MODE",
    }


def test_00_and_0i_outputs_are_required_but_not_computed() -> None:
    outputs = _report()["prepared_output_register"]
    assert outputs["output_count"] == 11
    assert outputs["computed_output_count"] == 0
    assert all(row["status"] == "NOT_COMPUTED" for row in outputs["rows"])
    assert all(row["value"] is None for row in outputs["rows"])
    ids = {row["output_id"] for row in outputs["rows"]}
    assert "STATIONARY_00_GREEN_FUNCTION" in ids
    assert "STATIONARY_0I_GREEN_FUNCTION" in ids
    assert "exact EH limit" in outputs["stationary_00_requirements"]
    assert "no orbital observable" in outputs["stationary_0i_requirements"]


def test_all_ten_controls_use_one_unexecuted_path() -> None:
    controls = _report()["shared_path_control_contract"]
    assert controls["control_count"] == 10
    assert controls["executed_control_count"] == 0
    assert [row["control_id"] for row in controls["rows"]] == [
        "C1_EH_BASELINE",
        "C2_SCALAR_REPRESENTATIVE",
        "C3_CURRENT_ZERO",
        "C4_CURRENT_SIGN",
        "C5_SOURCE_CONSERVATION",
        "C6_HEAVY_MODE_LIMIT",
        "C7_DERIVED_SCALAR_DEGENERACY",
        "C8_GAUGE_SECTOR",
        "C9_DIMENSIONS_NORMALIZATION",
        "C10_GAUSS_BONNET_LOCAL_BULK",
    ]
    assert all(row["uses_shared_derivation_path"] is True for row in controls["rows"])
    assert all(row["status"] == "NOT_EXECUTED" for row in controls["rows"])
    assert all(row["result"] is None for row in controls["rows"])
    assert controls["coefficient_fitting_prohibited"] is True


def test_fail_closed_conditions_cover_normalization_domains_and_controls() -> None:
    conditions = _report()["fail_closed_conditions"]
    for phrase in (
        "curvature Fourier gauge source or index sign ambiguity",
        "Einstein-Hilbert or source normalization ambiguity",
        "Gauss-Bonnet domain ambiguity",
        "unresolved degenerate pole or noninvertible operator",
        "source nonconservation",
        "Einstein control not reproduced without coefficient fitting",
    ):
        assert phrase in conditions


def test_fifteen_preparation_controls_pass() -> None:
    controls = _report()["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 15
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])


def test_scope_stops_before_every_scientific_calculation() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_executed"] is True
    assert scope["independent_packet_review_executed"] is False
    for key, value in scope.items():
        if key not in {"packet_preparation_executed", "independent_packet_review_executed"}:
            assert value is False, key


def test_human_packet_freezes_action_source_conventions_controls_and_stop() -> None:
    text = (REPO_ROOT / packet.HUMAN_PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "COMPARISON ACTION FAMILY",
        "A_EH  := c^3 / (16 pi G)",
        "delta S_ext |_eta",
        "alpha_reduced = alpha_unreduced - gamma",
        "eta_mu_nu = diag(+1,-1,-1,-1)",
        "exp[-i k.x] = exp[i(bold_k dot bold_x - omega t)]",
        "de Donder condition: F_nu = 0",
        "massive spin-2 candidate",
        "C1_EH_BASELINE",
        "comparison execution:    NOT AUTHORIZED",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
