from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-"
    "OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_COMPANION_OPERATOR_"
    "RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_exact_generic_frozen_"
    "companion_operator_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "derive_qft_gr_quadratic_component_expanded_"
    "generic_background_linearization_v0"
)


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    audit = calculation["generic_operator_closure_audit"]
    control = calculation["exact_minkowski_control"]
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]
    entries = control["sparse_entries"]
    entry_map = {
        (int(row["row"]), int(row["column"])): str(row["value"])
        for row in entries
    }
    duplicate_free = len(entry_map) == len(entries)
    expected_blockers = {
        "Q^H_mn",
        "Q_mn(g,c)",
        "L^S_mn",
        "partial_a F^R",
        "partial_a F^g_mn",
    }
    requirements = {
        row["id"]: row["status"] for row in audit["closure_requirements"]
    }

    checks = {
        "authorized_target_was_consumed": (
            calculation["execution_target"]
            == (
                "derive_qft_gr_quadratic_exact_generic_frozen_"
                "companion_operator_v0"
            )
            and calculation["selected_next_target"]
            == EXPECTED_CURRENT_TARGET
        ),
        "generic_operator_fails_closed": (
            audit["answer"] is False
            and audit["terminal_outcome"]
            == "GENERIC_BACKGROUND_OPERATOR_NOT_YET_CLOSED"
            and claims["exact_generic_background_operator_derived"]
            is False
            and claims["generic_characteristic_asymptotics_derived"]
            is False
            and claims["generic_finite_loss_established"] is False
            and claims["generic_fractional_root_splitting_excluded"]
            is False
        ),
        "all_named_predecessor_remainders_are_exposed": (
            set(audit["blocking_placeholders_found_in_predecessor"])
            == expected_blockers
            and requirements["QH_COMPONENT_EXPANSION"] == "BLOCKED"
            and requirements[
                "TENSOR_BOX_REMAINDER_COMPONENT_EXPANSION"
            ]
            == "BLOCKED"
            and requirements["DERIVATIVE_EQUATION_EXPANSION"]
            == "BLOCKED"
        ),
        "background_and_gauge_jets_fail_closed": (
            requirements["PRESCRIBED_GAUGE_SOURCE_JET"] == "BLOCKED"
            and requirements["INDEPENDENT_ON_SHELL_BACKGROUND_JET"]
            == "BLOCKED"
            and requirements[
                "GENERIC_128_STATE_COEFFICIENT_JACOBIANS"
            ]
            == "BLOCKED"
        ),
        "zero_addition_extension_remains_frozen": (
            requirements["ZERO_ADDITION_OFF_CONSTRAINT_EXTENSION"]
            == "PASS"
            and audit["off_constraint_extension"][
                "constraint_addition_M_A_B"
            ]
            == "identically zero"
            and audit["off_constraint_extension"][
                "derivative_constraint_addition_N_A_B_mu"
            ]
            == "identically zero"
        ),
        "minkowski_control_matrix_is_complete_and_placeholder_free": (
            control["classification"]
            == (
                "MINKOWSKI_FROZEN_COMPANION_OPERATOR_EXACTLY_"
                "DERIVED_CONTROL_ONLY"
            )
            and control["matrix_shape"] == [128, 128]
            and control["nonzero_entry_count"] == 224
            and duplicate_free
            and control["placeholder_free"] is True
            and control["generic_background_conclusion"] is False
            and control["sparse_entry_sha256"]
            == sha256_bytes(canonical_json_bytes(entries))
        ),
        "minkowski_top_identity_block_is_exact": all(
            entry_map.get((row, 64 + row)) == "1"
            for row in range(64)
        ),
        "minkowski_metric_scalar_and_spin_blocks_are_exact": (
            entry_map[(64, 50)] == "-1/2"
            and entry_map[(68, 50)] == "1/2"
            and entry_map[(64, 55)] == "2"
            and entry_map[(114, 50)]
            == "-k1**2 - k2**2 - k3**2 - m_R"
        ),
        "minkowski_derivative_blocks_are_exact": (
            entry_map[(115, 114)] == "-m_R"
            and entry_map[(116, 50)] == "-I*k1*m_R"
            and entry_map[(74, 114)] == "-1/2"
            and entry_map[(74, 119)] == "2"
        ),
        "minkowski_spin2_block_is_exact": (
            entry_map[(119, 50)] == "-a*m_R/4"
            and entry_map[(119, 115)] == "-a"
            and entry_map[(119, 55)]
            == "-k1**2 - k2**2 - k3**2 + m_S"
            and entry_map[(126, 50)] == "a*m_R/4"
            and entry_map[(126, 53)] == "-I*a*k2"
        ),
        "constraint_projector_remains_deferred": (
            requirements["FULL_CONSTRAINT_TANGENT_PROJECTOR"]
            == "DEFERRED_NOT_REQUIRED_FOR_UNRESTRICTED_OPERATOR"
            and claims["constraint_tangent_projector_constructed"]
            is False
            and claims[
                "constraint_restricted_minimum_loss_established"
            ]
            is False
        ),
        "no_spectral_variable_or_nonlinear_overclaim": (
            prohibitions["named_remainder_inserted_as_exact_matrix_entry"]
            is False
            and prohibitions["minkowski_control_called_generic"] is False
            and prohibitions["order_graph_called_spectral_proof"] is False
            and prohibitions["constraint_projection_inferred"] is False
            and claims["variable_coefficient_estimate_established"]
            is False
            and claims["quasilinear_estimate_established"] is False
            and claims["local_well_posedness_established"] is False
            and prohibitions["source_extension_executed"] is False
            and prohibitions["ghost_analysis_executed"] is False
            and prohibitions["phenomenology_executed"] is False
            and prohibitions["yukawa_work_executed"] is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_COMPANION_"
            "OPERATOR_RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_CURRENT_TARGET,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_calculation_module": False,
            "recomputes_sparse_entry_hash": True,
            "recomputes_top_identity_coverage": True,
            "checks_exact_representative_entries_in_every_block": True,
            "rechecks_predecessor_placeholder_set": True,
            "fails_closed_on_generic_operator_and_spectrum": True,
            "fails_closed_on_constraint_projector": True,
            "audits_claim_ceiling": True,
        },
        "accepted_results": (
            [
                (
                    "MINKOWSKI_FROZEN_COMPANION_OPERATOR_EXACTLY_"
                    "DERIVED_CONTROL_ONLY"
                ),
                "GENERIC_BACKGROUND_OPERATOR_NOT_YET_CLOSED",
                (
                    "GENERIC_SUBPRINCIPAL_SPECTRAL_CLASSIFICATION_"
                    "NOT_AUTHORIZED"
                ),
                "CONSTRAINT_TANGENT_PROJECTOR_REMAINS_BLOCKED",
                "NO_VARIABLE_OR_NONLINEAR_ESTIMATE",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "EXACT_GENERIC_BACKGROUND_FROZEN_COMPANION_OPERATOR",
            "GENERIC_CHARACTERISTIC_ROOT_ASYMPTOTICS",
            "GENERIC_FINITE_SOBOLEV_LOSS",
            "GENERIC_FRACTIONAL_ROOT_SPLITTING_EXCLUSION",
            "FULL_128_STATE_CONSTRAINT_TANGENT_PROJECTOR",
            "CONSTRAINT_RESTRICTED_MINIMUM_FROZEN_LOSS",
            "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
            "QUASILINEAR_TAME_ESTIMATE",
            "LOCAL_EXISTENCE",
            "UNIQUENESS",
            "CONTINUOUS_DEPENDENCE",
        ],
        "authority_rotation": {
            "generic_operator_execution_result_accepted": accepted,
            "component_expanded_background_linearization_authorized": (
                accepted
            ),
            "generic_spectral_calculation_authorized": False,
            "constraint_tangent_projection_authorized": False,
            "variable_coefficient_estimate_authorized": False,
            "quasilinear_estimate_authorized": False,
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
                "repair_qft_gr_quadratic_exact_generic_frozen_"
                "companion_operator_v0"
            )
        ),
        "verdict": (
            "ACCEPT_EXACT_MINKOWSKI_CONTROL_KEEP_GENERIC_OPERATOR_"
            "SPECTRUM_AND_CONSTRAINT_MINIMUM_BLOCKED_AUTHORIZE_"
            "COMPONENT_EXPANDED_GENERIC_BACKGROUND_LINEARIZATION_ONLY_"
            "NO_VARIABLE_OR_NONLINEAR_ESTIMATE"
            if accepted
            else (
                "B_BLOCKED_EXACT_GENERIC_FROZEN_COMPANION_RESULT_"
                "REQUIRES_CORRECTION"
            )
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity exact generic frozen companion "
            "operator result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
