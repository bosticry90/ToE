from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_reduction_with_transverse_fields as repair


def test_full_zero_mode_repair_artifacts_are_current() -> None:
    packet, manifest, report = repair.build_artifacts()
    assert repair.PACKET_PATH.read_bytes() == repair.canonical_json_bytes(packet)
    assert repair.MANIFEST_PATH.read_bytes() == repair.canonical_json_bytes(manifest)
    assert repair.REPORT_PATH.read_bytes() == repair.canonical_json_bytes(report)


def test_complete_parent_field_inventory_is_retained() -> None:
    packet, _, _ = repair.build_artifacts()
    inventory = packet["field_inventory"]
    assert inventory["longitudinal_gauge_field"] == ["A_0(t,x)", "A_1(t,x)"]
    assert inventory["transverse_gauge_descendants"] == ["phi_2(t,x):=A_2(t,x)", "phi_3(t,x):=A_3(t,x)"]
    assert inventory["total_two_component_spinors"] == 4
    assert inventory["sector_projection_used"] is False
    assert inventory["transverse_descendants_are_new_independent_scalar_matter"] is False


def test_Maxwell_decomposition_gives_two_positive_scalar_kinetics() -> None:
    packet, _, _ = repair.build_artifacts()
    decomposition = packet["field_strength_decomposition"]
    assert decomposition["F_MN_F^MN"] == "F_ab F^ab-2 partial_a phi_2 partial^a phi_2-2 partial_a phi_3 partial^a phi_3"
    terms = {item["term_id"]: item for item in packet["reduced_action"]["terms"]}
    assert terms["phi2_kinetic"]["internal_expression"].startswith("+")
    assert terms["phi3_kinetic"]["internal_expression"].startswith("+")
    assert all(item["introduced_to_repair_conservation"] is False for item in terms.values())


def test_transverse_equations_and_sector_couplings_are_present() -> None:
    packet, _, _ = repair.build_artifacts()
    equations = packet["reduced_equations"]
    assert equations["phi2"] == "Box phi_2=mu_0 J_2=-mu_0 J^2"
    assert equations["phi3"] == "Box phi_3=mu_0 J_3=-mu_0 J^3"
    assert "gamma^2 phi_2" in equations["Dirac_plus"]
    assert "gamma^3 phi_3" in equations["Dirac_minus"]
    assert packet["gamma_sector_structure"]["transverse_couplings_mix_retained_sectors"] is True


def test_variation_stress_dimensions_and_exchange_close() -> None:
    packet, _, _ = repair.build_artifacts()
    assert len(packet["variation_reduction_commutation"]["checks"]) == 6
    assert packet["variation_reduction_commutation"]["all_residuals_zero"] is True
    assert packet["stress_energy"]["C_T_reduction"] == "0"
    assert packet["dimension_order_audit"]["all_zero"] is True
    assert len(packet["exchange_structure"]["channels"]) == 3
    assert packet["exchange_structure"]["all_channels_cancel"] is True
    assert packet["exchange_structure"]["overall_total_conservation"] == "partial_a T_total^ab=0"


def test_blocker_regression_and_control_inventory_are_frozen() -> None:
    packet, _, _ = repair.build_artifacts()
    controls = packet["analytic_controls"]
    assert len(controls["positive"]) == 8
    assert len(controls["negative"]) == 11
    assert "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT" in controls["permanent_regression_control"]


def test_only_independent_analytic_review_is_authorized() -> None:
    packet, _, report = repair.build_artifacts()
    assert packet["selected_next_target"] == repair.REVIEW_TARGET
    assert packet["boundary"]["analytic_repair_accepted_before_review"] is False
    assert packet["boundary"]["numerical_guardrail_authorized"] is False
    assert packet["boundary"]["execution_authorized"] is False
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"


def test_prompt_is_preserved() -> None:
    assert repair.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
