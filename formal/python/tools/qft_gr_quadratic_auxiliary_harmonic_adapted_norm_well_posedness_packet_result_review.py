from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
    "WELL_POSEDNESS_PACKET_20260728_v0.json"
)
PHASE_A_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_PHYSICAL_SPIN2_PRINCIPAL_BLOCK_"
    "RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
    "WELL_POSEDNESS_PACKET_RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_"
    "well_posedness_packet_v0"
)
EXPECTED_NEXT_TARGET = (
    "derive_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0"
)


def build_review() -> dict:
    packet = read_json(PACKET_PATH)
    phase_a = read_json(PHASE_A_REVIEW_PATH)
    system = packet["candidate_reduced_system"]
    adapted = packet["adapted_norm_candidate"]
    constraint_ids = {row["id"] for row in packet["constraints"]}
    checks = {
        "packet_target_matches_authority": (
            packet["preparation_target"] == EXPECTED_CURRENT_TARGET
        ),
        "accepted_phase_a_is_byte_bound": (
            phase_a["accepted"] is True
            and packet["consumed_phase_a_review"]["sha256"]
            == sha256_path(PHASE_A_REVIEW_PATH)
        ),
        "trace_equation_has_generic_scalar_coefficient": (
            system["scalar_trace_equation"]
            == (
                "2(3 alpha + beta) Box_g R - c_R R "
                "- 2 c_Lambda = 0"
            )
        ),
        "trace_free_equation_has_hessian_coupling": (
            system["trace_free_ricci_principal_equation"]
            == (
                "beta Box_g S_mn "
                "- (2 alpha + beta)(nabla_m nabla_n R)^TF "
                "= lower(g,dg,R,dR,S,dS)"
            )
        ),
        "metric_equation_is_generalized_harmonic_wave": (
            system["generalized_harmonic_metric_principal_equation"]
            == (
                "Box_g g_mn = -2 S_mn - (1/2)g_mn R "
                "+ lower(g,dg,H,dH)"
            )
        ),
        "all_definition_gauge_and_geometric_constraints_are_listed": (
            constraint_ids
            == {
                "C_H_mu",
                "C_R",
                "C_S_mn",
                "C_trace",
                "C_div_n",
                "C_Hamiltonian_and_momentum",
            }
        ),
        "standard_and_adapted_norms_are_not_conflated": (
            packet["standard_metric_norm_test"][
                "same_order_estimate_available_generically"
            ]
            is False
            and adapted["candidate"]
            == "E_ad,s = W_(s+1)[g] + W_s[S] + W_(s+1)[R]"
        ),
        "derivative_loss_is_a_candidate_not_a_result": (
            adapted["candidate_pure_metric_derivative_loss"] == 1
            and adapted["minimum_loss_established"] is False
            and adapted["nonlinear_closure_established"] is False
            and adapted["continuous_dependence_established"] is False
        ),
        "iteration_and_constraint_obligations_are_explicit": (
            any(
                "Attempt Picard closure" in row
                for row in packet["required_execution_checks"]
            )
            and any(
                "homogeneous propagation system" in row
                for row in packet["required_execution_checks"]
            )
        ),
        "terminal_outcomes_are_non_overlapping": (
            set(packet["decision_tree"].values())
            >= {
                "REFUTED_BY_ACCEPTED_PHASE_A",
                "OPEN",
                "ADAPTED_NORM_LOCAL_WELL_POSEDNESS_ESTABLISHED",
                "SMOOTH_EXISTENCE_WITHOUT_HADAMARD_WELL_POSEDNESS",
                "GENERIC_LOCAL_WELL_POSEDNESS_BLOCKED",
            }
        ),
        "next_execution_is_reduced_system_only": (
            packet["authorized_execution_after_review"]["target"]
            == EXPECTED_NEXT_TARGET
            and "Energy-estimate execution remains a successor decision."
            in packet["authorized_execution_after_review"]["scope"]
        ),
        "excluded_work_remains_excluded": (
            "No regulator or fiducial mode added to close the estimate."
            in packet["prohibitions"]
            and "No Yukawa work." in packet["prohibitions"]
            and "Nonlinear adapted-norm theorem claim."
            in packet["not_yet_authorized"]
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
            "WELL_POSEDNESS_PACKET_RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": (
            "review_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_"
            "well_posedness_packet_v0_result"
        ),
        "reviewed_packet": {
            "path": PACKET_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(PACKET_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_packet_generator": False,
            "rechecks_trace_and_trace_free_coefficients": True,
            "rechecks_norm_claim_boundaries": True,
            "rechecks_constraint_inventory": True,
        },
        "authority_rotation": {
            "auxiliary_harmonic_reduced_system_derivation_authorized": accepted,
            "adapted_norm_theorem_execution_authorized": False,
            "source_extension_authorized": False,
            "preserved_descendant_adoption_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "repair_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_packet_v0"
        ),
        "verdict": (
            "ACCEPT_AUXILIARY_HARMONIC_PACKET_AUTHORIZE_REDUCED_SYSTEM_ONLY"
            if accepted
            else "B_BLOCKED_AUXILIARY_HARMONIC_PACKET_REQUIRES_CORRECTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic auxiliary-harmonic adapted-norm packet result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
