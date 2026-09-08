from __future__ import annotations

from formal.python.tools import maxwell_dirac_unit_object_foundation as foundation


def test_foundation_artifacts_are_current() -> None:
    packet, manifest, report = foundation.build_artifacts()
    assert foundation.PACKET_PATH.read_bytes() == foundation.canonical_json_bytes(packet)
    assert foundation.MANIFEST_PATH.read_bytes() == foundation.canonical_json_bytes(manifest)
    assert foundation.REPORT_PATH.read_bytes() == foundation.canonical_json_bytes(report)


def test_foundation_internal_dimensions_match_D4_and_D2() -> None:
    packet, _, _ = foundation.build_artifacts()
    d4 = packet["internal_mass_dimension_formula"]["D4"]
    d2 = packet["internal_mass_dimension_formula"]["D2"]
    assert d4 == {
        "psi": "3/2",
        "A_mu": "1",
        "F_munu": "2",
        "q": "0",
        "j_number_mu": "3",
        "J_em_mu_equals_q_times_j": "3",
        "Lagrangian_density": "4",
        "stress_energy": "4",
    }
    assert d2 == {
        "psi": "1/2",
        "A_mu": "0",
        "F_munu": "1",
        "q": "1",
        "j_number_mu": "1",
        "J_em_mu_equals_q_times_j": "2",
        "Lagrangian_density": "2",
        "stress_energy": "2",
    }


def test_foundation_external_dimensions_and_order_audits_close() -> None:
    packet, _, _ = foundation.build_artifacts()
    assert len(packet["external_dimension_ledger"]) >= 25
    assert len(packet["dimension_checks"]) == 12
    assert all(item["passed"] and item["residual_vector"] == ["0"] * 5 for item in packet["dimension_checks"])
    assert len(packet["C_dim_order_checks"]) == 9
    assert all(item["passed"] and item["C_dim_order_residual"] == ["0"] * 5 for item in packet["C_dim_order_checks"])


def test_foundation_uses_two_cnumber_species_and_one_action() -> None:
    packet, _, _ = foundation.build_artifacts()
    assert packet["field_semantics"]["spinor_type"] == "commuting complex c-number spinor"
    assert packet["shared_action"]["species"] == [
        {"species_id": "psi_plus", "mass": "m", "charge": "+q"},
        {"species_id": "psi_minus", "mass": "m", "charge": "-q"},
    ]
    assert packet["shared_action"]["real_symmetrized"] is True
    assert "not quantum pair creation" in packet["field_semantics"]["spectral_diagnostics"][-1]


def test_foundation_derives_Hilbert_exchange_without_early_reduction() -> None:
    packet, _, _ = foundation.build_artifacts()
    derivation = packet["tetrad_variation_derivation"]
    assert derivation["canonical_route"] == "HILBERT_TENSOR_FROM_ORIENTED_TETRAD_VARIATION"
    assert derivation["policy_selected_tensor_used"] is False
    assert packet["derived_equations"]["Maxwell_exchange"].startswith("nabla_mu T_EM")
    assert packet["derived_equations"]["matter_exchange"].startswith("nabla_mu sum_s T_D")
    assert packet["derived_equations"]["total_conservation"].endswith("=0")
    assert packet["boundary"]["reduction_authorized"] is False
    assert packet["resolution_execution_readiness_candidate"]["authoritative_before_review"] is False


def test_foundation_preserves_nonclaims_and_prompt() -> None:
    packet, _, _ = foundation.build_artifacts()
    assert "no stable classical fermionic matter theory" in packet["nonclaims"]
    assert packet["boundary"]["C_k_audit_only"] is True
    assert packet["boundary"]["master_action_promoted"] is False
    assert foundation.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
