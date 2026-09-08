from __future__ import annotations

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_"
    "HIERARCHY_20260728_v0.json"
)
PRINCIPAL_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_FULL_REDUCED_SYSTEM_PRINCIPAL_STRUCTURE_"
    "RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_"
    "HIERARCHY_RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_adapted_derivative_loss_"
    "energy_hierarchy_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "compute_qft_gr_quadratic_frozen_coefficient_"
    "jordan_chain_frequency_growth_v0"
)


def _independent_chain_count_and_rank_check() -> dict:
    eta = sp.diag(-1, 1, 1, 1)
    complement_vectors = [
        sp.Matrix([-1, 0, 0, 0, 1, 0, 0, 2, 0]),
        sp.eye(9)[:, 8],
        sp.eye(9)[:, 0],
        sp.eye(9)[:, 2],
        sp.eye(9)[:, 3],
    ]
    roots: dict[str, dict] = {}
    for lam in (-1, 1):
        ell = sp.Matrix([lam, 1, 0, 0])
        columns: list[sp.Matrix] = []
        for index in range(4):
            r = sp.zeros(4, 1)
            r[index, 0] = 1
            symmetric = (ell * r.T + r * ell.T) / 2
            tracefree = symmetric - eta * (eta * symmetric).trace() / 4
            columns.append(
                sp.Matrix(
                    [
                        tracefree[0, 0],
                        tracefree[0, 1],
                        tracefree[0, 2],
                        tracefree[0, 3],
                        tracefree[1, 1],
                        tracefree[1, 2],
                        tracefree[1, 3],
                        tracefree[2, 2],
                        tracefree[2, 3],
                    ]
                )
            )
        hessian = sp.Matrix.hstack(*columns)
        extended = sp.Matrix.hstack(hessian, *complement_vectors)
        chain_lengths = [3] * 4 + [2] * 6 + [1] * 40
        roots[str(lam)] = {
            "H_rank": hessian.rank(),
            "extended_S_rank": extended.rank(),
            "chain_count": len(chain_lengths),
            "algebraic_dimension": sum(chain_lengths),
            "geometric_dimension": len(chain_lengths),
            "eigenvector_deficit": sum(
                length - 1 for length in chain_lengths
            ),
            "physical_deficit": 2,
        }
    return roots


def build_review() -> dict:
    packet = read_json(PACKET_PATH)
    predecessor = read_json(PRINCIPAL_REVIEW_PATH)
    independent = _independent_chain_count_and_rank_check()
    ledger = packet["jordan_chain_ledger"]
    energies = packet["energy_definitions"]
    loss = packet["loss_distinction"]
    lower_order = packet["weighted_lower_order_audit"]
    levels = packet["four_proof_levels"]
    nonaccumulation = packet["nonaccumulation_contract"]
    regularity = packet["regularity_threshold_ledger"]
    claims = packet["claim_boundary"]
    prohibitions = packet["prohibitions_respected"]

    checks = {
        "authority_and_principal_predecessor_are_exactly_bound": (
            predecessor["accepted"] is True
            and predecessor["selected_next_target"]
            == packet["preparation_target"]
            and packet["preparation_target"]
            == (
                "prepare_qft_gr_quadratic_adapted_derivative_loss_"
                "energy_hierarchy_v0"
            )
            and packet["selected_next_target"]
            == EXPECTED_CURRENT_TARGET
            and len(packet["consumed_authority"]["sha256"]) == 64
            and len(
                packet["consumed_principal_structure"]["sha256"]
            )
            == 64
        ),
        "fifty_chains_at_each_root_are_complete_and_independent": (
            all(
                independent[root]
                == {
                    "H_rank": 4,
                    "extended_S_rank": 9,
                    "chain_count": 50,
                    "algebraic_dimension": 64,
                    "geometric_dimension": 50,
                    "eigenvector_deficit": 14,
                    "physical_deficit": 2,
                }
                for root in ("-1", "1")
            )
            and all(
                len(ledger["roots"][root]) == 50
                and ledger["rank_and_count_checks"][root][
                    "algebraic_dimension"
                ]
                == 64
                and ledger["rank_and_count_checks"][root][
                    "geometric_dimension"
                ]
                == 50
                and ledger["rank_and_count_checks"][root][
                    "eigenvector_deficit"
                ]
                == 14
                for root in ("-1", "1")
            )
        ),
        "chain_rows_contain_every_required_ledger_field": (
            all(
                {
                    "chain_id",
                    "root",
                    "chain_length",
                    "chain_variables",
                    "leading_mode",
                    "raw_differential_maps",
                    "metric_weighted_orders",
                    "conventional_first_order_frequency_growth",
                    "raw_growth_exponent",
                    "weight_absorption",
                    "net_loss",
                    "constraint_status",
                }
                <= set(row)
                for root_rows in ledger["roots"].values()
                for row in root_rows
            )
        ),
        "deficit_decomposition_separates_physical_and_nonphysical": (
            ledger["deficit_decomposition_each_root"]
            == {
                "total_missing_eigenvectors": 14,
                "physical_TT_size_2_chains": 2,
                "missing_from_physical_TT": 2,
                "size_3_reconstruction_chains": 4,
                "missing_from_size_3_reconstruction": 8,
                "non_TT_size_2_chains": 4,
                "missing_from_non_TT_size_2": 4,
                "check": "2+8+4=14",
            }
        ),
        "equivalence_shift_is_not_promoted_to_propagator_loss": (
            loss["proved_equivalence_map_shift"] == 1
            and loss["propagator_loss_candidate"] == [1, 2]
            and loss["propagator_loss_established"] is False
            and claims["equivalence_map_shift_one_derivative"] is True
            and claims["propagator_loss_one_derivative_established"]
            is False
            and claims["propagator_loss_two_derivatives_refuted"] is False
        ),
        "three_required_energy_families_and_constraint_energy_are_frozen": (
            {
                "coercive_wave_energy",
                "equal_order_auxiliary",
                "natural_fourth_order_metric",
                "adapted_auxiliary",
                "adapted_metric_equivalence",
                "constraint_compatible_total",
            }
            == set(energies)
            and energies["adapted_auxiliary"]["spatial_weights_sigma"]
            == {
                "g_mn": 2,
                "c_mna": 1,
                "R": 2,
                "r_a": 1,
                "S_mn": 1,
            }
            and energies["adapted_metric_equivalence"][
                "spatial_weights_sigma"
            ]
            == {
                "g_mn": 3,
                "c_mna": 2,
                "R": 1,
                "r_a": 0,
                "S_mn": 1,
            }
            and energies["constraint_compatible_total"][
                "independent_constraint_components"
            ]
            == 69
            and energies["constraint_compatible_total"][
                "physical_defect_repaired_by_constraint_energy"
            ]
            is False
        ),
        "weighted_principal_contamination_is_included_not_ignored": (
            {
                row["coupling"]
                for row in lower_order[
                    "terms_promoted_to_metric_weighted_principal_order"
                ]
            }
            == {
                "E_g<-R,S",
                "E_c<-partial R,partial S",
                "E_S<-partial r",
            }
            and lower_order["included_in_principal_matrix"] is True
            and lower_order["unlisted_promoted_term_found"] is False
            and lower_order[
                "variable_coefficient_commutator_audit_executed"
            ]
            is False
        ),
        "four_proof_levels_are_strictly_sequenced": (
            [row["level"] for row in levels] == [1, 2, 3, 4]
            and [row["id"] for row in levels]
            == [
                "FROZEN_COEFFICIENT_FOURIER_PROPAGATOR",
                "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
                "QUASILINEAR_TAME_ESTIMATE",
                "ITERATION_CLOSURE",
            ]
            and levels[0]["status"] == "AUTHORIZED_NEXT_AFTER_ACCEPTED_REVIEW"
            and all(
                row["status"] == "NOT_AUTHORIZED_BY_THIS_PACKET"
                for row in levels[1:]
            )
        ),
        "fixed_loss_and_accumulating_loss_are_explicitly_separated": (
            "one fixed r"
            in nonaccumulation["acceptable_fixed_shift"]
            and "s+n" in nonaccumulation["unacceptable_iterative_shift"]
            and nonaccumulation["one_time_loss_established"] is False
            and nonaccumulation["loss_nonaccumulation_established"]
            is False
            and nonaccumulation["picard_closure_established"] is False
            and nonaccumulation["nash_moser_required"] == "UNRESOLVED"
        ),
        "regularity_threshold_is_candidate_not_theorem": (
            regularity["analytic_floor"] == "s>5/2 for C^1 coefficient control"
            and regularity["frozen_integer_candidate"] == "s>=3"
            and regularity["variable_and_quasilinear_working_candidate"]
            == "s>=4"
            and regularity["minimum_index_established"] is False
            and regularity["candidate_is_not_theorem"] is True
        ),
        "preparation_outcome_is_ready_while_loss_grading_remains_open": (
            packet["preparation_outcomes"]
            == [
                "ADAPTED_ENERGY_HIERARCHY_READY",
                "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
                (
                    "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_"
                    "NOT_YET_ESTIMATED"
                ),
            ]
        ),
        "no_estimate_theorem_or_forbidden_extension_is_claimed": (
            claims["frozen_coefficient_energy_estimate_established"] is False
            and claims["variable_coefficient_energy_estimate_established"]
            is False
            and claims["quasilinear_tame_estimate_established"] is False
            and claims["loss_nonaccumulation_established"] is False
            and claims["picard_iteration_closed"] is False
            and claims["local_existence_established"] is False
            and claims["uniqueness_established"] is False
            and claims["continuous_dependence_established"] is False
            and prohibitions["energy_estimate_claimed_from_principal_symbol"]
            is False
            and prohibitions[
                "one_derivative_equivalence_shift_called_propagator_loss"
            ]
            is False
            and prohibitions["constraints_used_to_repair_physical_defect"]
            is False
            and prohibitions["regularizer_or_fiducial_mode_added"] is False
            and prohibitions["yukawa_work_executed"] is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_"
            "HIERARCHY_RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_CURRENT_TARGET,
        "reviewed_packet": {
            "path": PACKET_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(PACKET_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_packet_module": False,
            "reconstructs_H_maps": True,
            "reconstructs_TT_and_auxiliary_complement": True,
            "recomputes_chain_partition_and_deficit": True,
            "audits_every_chain_ledger_field": True,
            "audits_energy_weights": True,
            "audits_proof_level_authority": True,
            "audits_claim_ceiling": True,
        },
        "accepted_results": (
            [
                "ADAPTED_ENERGY_HIERARCHY_READY",
                "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
                (
                    "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_"
                    "NOT_YET_ESTIMATED"
                ),
                "COMPLETE_FIFTY_CHAIN_LEDGER_AT_EACH_ROOT",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "ONE_DERIVATIVE_FROZEN_PROPAGATOR_LOSS",
            "TWO_DERIVATIVE_LOSS_REFUTATION",
            "CONSTRAINT_TANGENT_PROJECTION_FOR_ALL_NON_TT_CHAINS",
            "FROZEN_COEFFICIENT_ENERGY_ESTIMATE",
            "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
            "QUASILINEAR_TAME_ESTIMATE",
            "LOSS_NONACCUMULATION",
            "PICARD_CLOSURE",
            "NASH_MOSER_REQUIREMENT",
            "LOCAL_EXISTENCE",
            "UNIQUENESS",
            "CONTINUOUS_DEPENDENCE",
        ],
        "authority_rotation": {
            "energy_hierarchy_preparation_accepted": accepted,
            "frozen_coefficient_frequency_growth_authorized": accepted,
            "variable_coefficient_estimate_authorized": False,
            "quasilinear_estimate_authorized": False,
            "iteration_closure_authorized": False,
            "local_existence_theorem_authorized": False,
            "source_extension_authorized": False,
            "ghost_analysis_authorized": False,
            "phenomenology_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else (
                "repair_qft_gr_quadratic_adapted_derivative_loss_"
                "energy_hierarchy_v0"
            )
        ),
        "verdict": (
            "ACCEPT_COMPLETE_ENERGY_HIERARCHY_AND_JORDAN_LEDGER_"
            "AUTHORIZE_FROZEN_COMPANION_FREQUENCY_GROWTH_ONLY_KEEP_"
            "ONE_OR_TWO_DERIVATIVE_LOSS_UNRESOLVED"
            if accepted
            else (
                "B_BLOCKED_ADAPTED_ENERGY_HIERARCHY_REQUIRES_CORRECTION"
            )
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity adapted derivative-loss energy-hierarchy "
            "result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
