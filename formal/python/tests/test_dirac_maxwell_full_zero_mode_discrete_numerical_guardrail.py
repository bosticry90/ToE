from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_discrete_numerical_guardrail as guardrail


def test_guardrail_artifacts_are_current() -> None:
    packet, manifest, report = guardrail.build_artifacts()
    assert guardrail.PACKET_PATH.read_bytes() == guardrail.canonical_json_bytes(packet)
    assert guardrail.MANIFEST_PATH.read_bytes() == guardrail.canonical_json_bytes(manifest)
    assert guardrail.REPORT_PATH.read_bytes() == guardrail.canonical_json_bytes(report)


def test_mixed_link_site_inventory_and_group_update_are_frozen() -> None:
    packet, _, _ = guardrail.build_artifacts()
    variables = packet["lattice_variables"]
    assert "group-valued links" in variables["A1"]
    assert variables["phi2_phi3"] == "real site fields"
    assert variables["Pi2_Pi3"].startswith("real site momenta")
    assert packet["link_update"]["preserves_unit_modulus_by_construction"] is True
    assert packet["link_update"]["componentwise_update_then_projection"] is False
    assert packet["link_update"]["negative_species_transport"] == "U*"


def test_Wilson_operator_dispersion_and_descendant_couplings_are_complete() -> None:
    packet, _, _ = guardrail.build_artifacts()
    operators = packet["spatial_operators"]
    assert operators["Wilson_parameter"] == 1
    assert operators["naive_centered_operator_role"] == "negative control only"
    assert "alpha2 phi2_n+alpha3 phi3_n" in operators["transverse_site_coupling"]
    assert packet["Wilson_dispersion"]["exact_discrete_comparison_each_grid"] is True
    assert packet["Wilson_dispersion"]["doubler_branch_separation_required"] is True


def test_discrete_symmetry_earns_constraints_and_holonomy_is_distinguished() -> None:
    packet, _, _ = guardrail.build_artifacts()
    symmetry = packet["discrete_symmetry_and_constraints"]
    assert symmetry["gauge_invariant_action_required"] is True
    assert "discrete Noether identity" in symmetry["continuity_identity"]
    assert "solver residual" in symmetry["Gauss_preservation"]
    assert packet["holonomy_controls"]["trivial"]["globally_pure_gauge"] is True
    assert packet["holonomy_controls"]["nontrivial"]["globally_pure_gauge"] is False


def test_energy_class_and_all_terms_are_honest() -> None:
    packet, _, _ = guardrail.build_artifacts()
    energy = packet["discrete_energy"]
    assert energy["classification"] == "BOUNDED_CONVERGENT_ENERGY_ERROR"
    assert len(energy["inventory"]) == 8
    assert energy["exact_continuum_energy_claimed"] is False
    assert energy["modified_Hamiltonian_claimed_exact"] is False
    assert packet["discrete_exchange"]["C_exchange_embedded_as_equation"] is False


def test_controls_and_pilot_boundary_are_complete() -> None:
    packet, _, _ = guardrail.build_artifacts()
    assert len(packet["controls"]["positive"]) == 12
    assert len(packet["controls"]["negative"]) == 27
    assert packet["controls"]["previous_blocker_permanent"] is True
    assert packet["pilot_policy"]["status"] == "PENDING_NONAUTHORITATIVE_PILOT"
    assert packet["pilot_policy"]["pilot_result_authoritative"] is False
    assert packet["pilot_policy"]["solver_rule"].startswith("solver error <=0.01")


def test_no_pilot_or_execution_is_authorized_before_review() -> None:
    packet, _, report = guardrail.build_artifacts()
    assert packet["selected_next_target"] == guardrail.REVIEW_TARGET
    assert packet["boundary"]["guardrail_accepted_before_review"] is False
    assert packet["boundary"]["non_authoritative_pilot_authorized"] is False
    assert packet["boundary"]["canonical_execution_authorized"] is False
    assert packet["boundary"]["result_claimed"] is False
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"


def test_prompt_is_preserved() -> None:
    assert guardrail.sha256_path(guardrail.REPO_ROOT / guardrail.PROMPT_RELATIVE_PATH) == guardrail.PROMPT_SHA256
