from __future__ import annotations

from formal.python.tools import dirac_maxwell_3p1_to_1p1_reduction_consistency as reduction


def test_reduction_artifacts_are_current() -> None:
    packet, manifest, report = reduction.build_artifacts()
    assert reduction.PACKET_PATH.read_bytes() == reduction.canonical_json_bytes(packet)
    assert reduction.MANIFEST_PATH.read_bytes() == reduction.canonical_json_bytes(manifest)
    assert reduction.REPORT_PATH.read_bytes() == reduction.canonical_json_bytes(report)


def test_four_dimensional_clifford_representation_reproduces() -> None:
    checks = reduction.clifford_checks()
    assert len(checks) == 10
    assert all(item["passed"] and item["max_residual"] == "0.0e+00" for item in checks)


def test_longitudinal_sector_split_and_transverse_mixing_are_explicit() -> None:
    packet, _, _ = reduction.build_artifacts()
    gamma = packet["gamma_representation"]
    assert gamma["A0_A1_coupling_does_not_mix_sectors"] is True
    assert gamma["A2_A3_coupling_mixes_sectors"] is True
    assert gamma["longitudinal_gamma_sector_mixing_norm"] == "0.0e+00"


def test_retained_sector_counterexample_sources_transverse_equation() -> None:
    counterexample = reduction.transverse_counterexample()
    assert counterexample["state_norm"] == "1"
    assert counterexample["both_sector_components_nonzero"] is True
    assert counterexample["at_least_one_transverse_current_nonzero"] is True
    assert abs(float(counterexample["j2"]["real"])) == 1.0


def test_full_zero_mode_system_passes_but_requested_truncation_blocks() -> None:
    packet, _, report = reduction.build_artifacts()
    assert packet["full_zero_mode_reduction"]["full_zero_mode_variation_reduction_commutes"] is True
    assert packet["proposed_transverse_truncation"]["constraint_surface_invariant_for_all_retained_sector_data"] is False
    assert packet["analytic_result"] == "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT"
    assert report["verdict"] == "PREPARED_B_BLOCKED_PENDING_INDEPENDENT_REVIEW"


def test_all_reduced_spinor_sectors_are_retained_without_projection() -> None:
    packet, _, _ = reduction.build_artifacts()
    multiplicity = packet["spinor_multiplicity"]
    assert multiplicity["two_1p1_sectors_per_original_4component_spinor"] is True
    assert multiplicity["opposite_charge_original_species_count"] == 2
    assert multiplicity["total_2component_reduced_spinors"] == 4
    assert multiplicity["one_sector_projected_away"] is False


def test_blocker_selects_only_review_and_no_fallback_or_numerics() -> None:
    packet, _, _ = reduction.build_artifacts()
    assert packet["selected_next_target"] == reduction.REVIEW_TARGET
    assert packet["post_block_route_decision_candidates"] == [
        "repair reduction",
        "adopt a native 1+1 model",
        "move to 2+1",
        "change the matter sector",
    ]
    assert packet["post_block_route_selected_automatically"] is False
    assert packet["blocker"]["numerical_guardrail_authorized"] is False
    assert packet["blocker"]["execution_authorized"] is False


def test_prompt_is_preserved() -> None:
    assert reduction.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
