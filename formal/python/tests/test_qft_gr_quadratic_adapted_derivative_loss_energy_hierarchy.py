from __future__ import annotations

from formal.python.tools import (
    qft_gr_quadratic_adapted_derivative_loss_energy_hierarchy as packet,
)
from formal.python.tools import (
    qft_gr_quadratic_adapted_derivative_loss_energy_hierarchy_result_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_packet_and_review_artifacts_are_current() -> None:
    assert packet.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        packet.build_packet()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_complete_fifty_chain_ledger_closes_at_each_root() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    ledger = artifact["jordan_chain_ledger"]
    for root in ("-1", "1"):
        rows = ledger["roots"][root]
        checks = ledger["rank_and_count_checks"][root]
        assert len(rows) == 50
        assert sum(row["chain_length"] == 3 for row in rows) == 4
        assert sum(row["chain_length"] == 2 for row in rows) == 6
        assert sum(row["chain_length"] == 1 for row in rows) == 40
        assert sum(row["chain_length"] for row in rows) == 64
        assert sum(row["chain_length"] - 1 for row in rows) == 14
        assert checks["H_rank"] == 4
        assert checks["H_plus_selected_S_complement_rank"] == 9
        assert checks["geometric_dimension"] == 50


def test_deficit_is_split_into_physical_and_reconstruction_parts() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    deficit = artifact["jordan_chain_ledger"][
        "deficit_decomposition_each_root"
    ]
    assert deficit == {
        "total_missing_eigenvectors": 14,
        "physical_TT_size_2_chains": 2,
        "missing_from_physical_TT": 2,
        "size_3_reconstruction_chains": 4,
        "missing_from_size_3_reconstruction": 8,
        "non_TT_size_2_chains": 4,
        "missing_from_non_TT_size_2": 4,
        "check": "2+8+4=14",
    }


def test_every_chain_records_growth_weights_and_constraint_status() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    required = {
        "chain_length",
        "chain_variables",
        "leading_mode",
        "raw_differential_maps",
        "conventional_first_order_frequency_growth",
        "weight_absorption",
        "net_loss",
        "constraint_status",
    }
    for rows in artifact["jordan_chain_ledger"]["roots"].values():
        assert all(required <= set(row) for row in rows)
        assert sum(
            row["leading_mode"].startswith("PHYSICAL_SPIN2")
            for row in rows
        ) == 2


def test_equivalence_shift_is_not_called_a_propagator_loss() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    loss = artifact["loss_distinction"]
    assert loss["proved_equivalence_map_shift"] == 1
    assert loss["propagator_loss_candidate"] == [1, 2]
    assert loss["propagator_loss_established"] is False
    claims = artifact["claim_boundary"]
    assert claims["propagator_loss_one_derivative_established"] is False
    assert claims["propagator_loss_two_derivatives_refuted"] is False


def test_all_energy_families_and_weights_are_frozen() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    energies = artifact["energy_definitions"]
    assert energies["adapted_auxiliary"]["spatial_weights_sigma"] == {
        "g_mn": 2,
        "c_mna": 1,
        "R": 2,
        "r_a": 1,
        "S_mn": 1,
    }
    assert energies["adapted_metric_equivalence"][
        "spatial_weights_sigma"
    ] == {
        "g_mn": 3,
        "c_mna": 2,
        "R": 1,
        "r_a": 0,
        "S_mn": 1,
    }
    assert energies["constraint_compatible_total"][
        "independent_constraint_components"
    ] == 69
    assert energies["constraint_compatible_total"][
        "physical_defect_repaired_by_constraint_energy"
    ] is False


def test_weighted_principal_terms_are_not_silently_lower_order() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    audit = artifact["weighted_lower_order_audit"]
    assert {
        row["coupling"]
        for row in audit["terms_promoted_to_metric_weighted_principal_order"]
    } == {
        "E_g<-R,S",
        "E_c<-partial R,partial S",
        "E_S<-partial r",
    }
    assert audit["included_in_principal_matrix"] is True
    assert audit["unlisted_promoted_term_found"] is False
    assert audit["variable_coefficient_commutator_audit_executed"] is False


def test_four_proof_levels_authorize_only_frozen_propagator() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    levels = artifact["four_proof_levels"]
    assert [row["level"] for row in levels] == [1, 2, 3, 4]
    assert levels[0]["id"] == "FROZEN_COEFFICIENT_FOURIER_PROPAGATOR"
    assert levels[0]["status"] == "AUTHORIZED_NEXT_AFTER_ACCEPTED_REVIEW"
    assert all(
        row["status"] == "NOT_AUTHORIZED_BY_THIS_PACKET"
        for row in levels[1:]
    )


def test_nonaccumulation_and_regularity_remain_open() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    contract = artifact["nonaccumulation_contract"]
    assert "one fixed r" in contract["acceptable_fixed_shift"]
    assert "s+n" in contract["unacceptable_iterative_shift"]
    assert contract["loss_nonaccumulation_established"] is False
    assert contract["picard_closure_established"] is False
    assert contract["nash_moser_required"] == "UNRESOLVED"
    regularity = artifact["regularity_threshold_ledger"]
    assert regularity["analytic_floor"] == "s>5/2 for C^1 coefficient control"
    assert regularity["variable_and_quasilinear_working_candidate"] == "s>=4"
    assert regularity["minimum_index_established"] is False


def test_review_accepts_only_frozen_frequency_growth_execution() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    assert artifact["accepted_results"] == [
        "ADAPTED_ENERGY_HIERARCHY_READY",
        "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
        (
            "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_"
            "NOT_YET_ESTIMATED"
        ),
        "COMPLETE_FIFTY_CHAIN_LEDGER_AT_EACH_ROOT",
    ]
    rotation = artifact["authority_rotation"]
    assert rotation["energy_hierarchy_preparation_accepted"] is True
    assert rotation["frozen_coefficient_frequency_growth_authorized"] is True
    assert rotation["variable_coefficient_estimate_authorized"] is False
    assert rotation["quasilinear_estimate_authorized"] is False
    assert rotation["iteration_closure_authorized"] is False
    assert rotation["local_existence_theorem_authorized"] is False
    assert all(review.build_review()["checks"].values())
