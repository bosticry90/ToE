from __future__ import annotations

import re

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-"
    "BACKGROUND-LINEARIZATION-v1.json"
)
STAGE_1_CONTRACT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-LINEARIZATION-"
    "GAUGE-AND-JET-CONTRACT-v0.json"
)
MINKOWSKI_CONTROL_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-"
    "OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_"
    "LINEARIZATION_V1_RESULT_REVIEW_20260729_v0.json"
)
EXPECTED_REVIEW_TARGET = (
    "review_qft_gr_quadratic_component_expanded_generic_background_"
    "linearization_v1_result"
)
EXPECTED_NEXT_TARGET = (
    "derive_qft_gr_quadratic_exact_frozen_companion_operator_v1"
)
NODE_REF = re.compile(r"@([A-Za-z][A-Za-z0-9_]*)")
SYMMETRIC_COMPONENTS = {
    "00",
    "01",
    "02",
    "03",
    "11",
    "12",
    "13",
    "22",
    "23",
    "33",
}


def _node_graph_checks(calculation: dict) -> dict[str, bool]:
    ledger = calculation["component_dag"]["nodes"]
    identifiers = [str(node["id"]) for node in ledger]
    identifier_set = set(identifiers)
    dependencies = {
        str(node["id"]): set(NODE_REF.findall(str(node["expression"])))
        for node in ledger
    }
    reference_closure = all(
        reference in identifier_set
        for references in dependencies.values()
        for reference in references
    )
    positions = {identifier: index for index, identifier in enumerate(identifiers)}
    topologically_ordered = all(
        positions[reference] < positions[identifier]
        for identifier, references in dependencies.items()
        for reference in references
    )
    ledger_hash = sha256_bytes(canonical_json_bytes(ledger))
    forbidden = ("Q^H", "L^S", "lower(", "O(", "background contributions")
    expressions = "\n".join(str(node["expression"]) for node in ledger)
    return {
        "node_ids_are_unique": len(identifiers) == len(identifier_set),
        "reference_closure": reference_closure,
        "topologically_ordered": topologically_ordered,
        "ledger_hash_matches": (
            ledger_hash == calculation["component_dag"]["node_ledger_sha256"]
        ),
        "node_count_matches": (
            len(ledger) == calculation["component_dag"]["node_count"] == 3950
        ),
        "unnamed_placeholders_absent": not any(
            token in expressions for token in forbidden
        ),
    }


def _equation_inventory_checks(calculation: dict) -> dict[str, bool]:
    equations = calculation["component_equations"]
    common = equations["common_equations"]
    common_ids = [str(row["id"]) for row in common]
    common_counts = {
        "g": sum(identifier.startswith("delta_Eg_") for identifier in common_ids),
        "R": sum(identifier == "delta_ER" for identifier in common_ids),
        "r": sum(identifier.startswith("delta_Er_") for identifier in common_ids),
        "c": sum(identifier.startswith("delta_Ec_") for identifier in common_ids),
    }
    charts = equations["tracefree_atlas_equations"]
    chart_pivots = {
        str(chart["chart_id"]).removeprefix("TRACEFREE_CHART_PIVOT_")
        for chart in charts
    }
    charts_are_nine_dimensional = all(
        chart["independent_component_count"] == 9
        and len(chart["equation_ids"]) == 9
        and len(set(chart["equation_ids"])) == 9
        and len(chart["component_expressions"]) == 9
        for chart in charts
    )
    pivot_is_eliminated = all(
        f"delta_ES_{str(chart['chart_id']).removeprefix('TRACEFREE_CHART_PIVOT_')}"
        not in chart["equation_ids"]
        for chart in charts
    )
    return {
        "common_inventory_is_55": (
            len(common) == 55
            and common_counts == {"g": 10, "R": 1, "r": 4, "c": 40}
        ),
        "ten_tracefree_charts_cover_all_pivots": (
            len(charts) == 10 and chart_pivots == SYMMETRIC_COMPONENTS
        ),
        "each_tracefree_chart_has_nine_equations": (
            charts_are_nine_dimensional and pivot_is_eliminated
        ),
        "independent_inventory_is_64_per_chart": (
            equations["component_counts"]
            == {"g": 10, "R": 1, "r": 4, "c": 40, "S": 9}
            and equations["equation_count_per_chart"] == 64
        ),
    }


def _minkowski_checks(calculation: dict) -> bool:
    regression = calculation["minkowski_regression"]
    control = read_json(MINKOWSKI_CONTROL_PATH)["exact_minkowski_control"]
    recomputed = sha256_bytes(canonical_json_bytes(control["sparse_entries"]))
    return (
        regression["classification"]
        == "MINKOWSKI_SPECIALIZATION_EXACTLY_REPRODUCED"
        and regression["matrix_shape"] == [128, 128]
        and regression["nonzero_entry_count"] == 224
        and regression["sparse_entry_sha256"] == recomputed
        and control["sparse_entry_sha256"] == recomputed
        and regression["entry_positions_and_coefficients_identical"] is True
        and regression["Fourier_convention_identical"] is True
        and regression["light_cone_roots_identical"] is True
        and regression["Jordan_chain_decomposition_identical"] is True
    )


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    contract = read_json(STAGE_1_CONTRACT_PATH)
    graph_checks = _node_graph_checks(calculation)
    inventory_checks = _equation_inventory_checks(calculation)
    forms = calculation["forms"]
    identities = calculation["identity_checks"]
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]
    checks = {
        "bounded_stage_2_open_event_consumed": (
            calculation["bounded_authority"]["attempt_sequence_number"] == 2
            and calculation["bounded_authority"]["program_id"]
            == "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
            and calculation["bounded_authority"]["semantic_stage_id"]
            == "COMPONENT_EXPANDED_LINEARIZATION"
            and len(calculation["bounded_authority"]["open_event_hash"]) == 64
        ),
        "accepted_stage_1_contract_is_byte_bound": (
            calculation["consumed_stage_1_contract"]["sha256"]
            == sha256_path(STAGE_1_CONTRACT_PATH)
            and contract["verdict"]
            == "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE"
        ),
        "component_graph_is_closed_acyclic_and_placeholder_free": all(
            graph_checks.values()
        ),
        "independent_64_equation_inventory_is_recomputed": all(
            inventory_checks.values()
        ),
        "off_shell_on_shell_and_gauge_forms_are_separate": (
            forms["off_shell"]["status"] == "OFF_SHELL_FORM_COMPLETE"
            and forms["off_shell"]["background_residuals_retained"] == 64
            and forms["on_shell"]["status"] == "ON_SHELL_REDUCTION_COMPLETE"
            and forms["on_shell"]["R6_applied_only_after_component_Jacobian"]
            is True
            and forms["gauge_compatible"]["status"]
            == "GAUGE_COMPATIBLE_FORM_COMPLETE"
            and forms["gauge_compatible"]["H_mu"] == "0"
            and forms["gauge_compatible"]["delta_H_mu"] == "0"
            and forms["gauge_compatible"]["constraint_additions"] == "ZERO"
        ),
        "component_identity_certificates_cover_required_families": (
            identities["component_count_is_derived_not_assumed"] is True
            and identities["inverse_metric_tangent"].startswith(
                "delta gInv^ab="
            )
            and identities["linearized_contracted_bianchi"].startswith("PASS_")
            and identities["trace_tracefree_recombination"].startswith("PASS_")
            and identities["divergence_of_tracefree_ricci_equation"].startswith(
                "PASS_"
            )
            and identities["definition_integrability"].startswith("PASS_")
            and identities["symmetry_and_tracefree"].startswith("PASS_")
        ),
        "all_ten_trace_charts_share_the_same_future_classification": (
            calculation["chart_overlap_invariance"][
                "same_characteristic_roots_required"
            ]
            is True
            and calculation["chart_overlap_invariance"][
                "same_Jordan_dimensions_required"
            ]
            is True
            and calculation["chart_overlap_invariance"][
                "same_finite_loss_classification_required"
            ]
            is True
            and calculation["chart_overlap_invariance"][
                "spectral_calculation_executed_here"
            ]
            is False
        ),
        "Minkowski_128_state_224_entry_control_is_exact": _minkowski_checks(
            calculation
        ),
        "stage_2_claim_ceiling_is_respected": (
            claims["component_background_linearization_complete"] is True
            and claims["exact_generic_companion_spectrum_derived"] is False
            and claims["constraint_tangent_improvement_established"] is False
            and claims["generic_polynomial_frequency_growth_established"]
            is False
            and claims["variable_coefficient_estimate_established"] is False
            and claims["nonlinear_local_well_posedness_established"] is False
            and claims["quadratic_gravity_physical_viability_established"]
            is False
            and prohibitions["generic_companion_constructed"] is False
            and prohibitions["spectral_asymptotics_computed"] is False
            and prohibitions["constraint_projector_constructed"] is False
            and prohibitions["subsidiary_scientific_target_created"] is False
        ),
        "only_bounded_stage_3_is_selected": (
            calculation["terminal_outcome"]
            == "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE"
            and calculation["selected_next_target"] == EXPECTED_NEXT_TARGET
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    calculation_bytes = CALCULATION_PATH.read_bytes()
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_"
            "LINEARIZATION_V1_RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_REVIEW_TARGET,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
            "canonical_sha256_recomputed": sha256_bytes(
                canonical_json_bytes(calculation)
            ),
            "canonical_bytes_match": (
                calculation_bytes == canonical_json_bytes(calculation)
            ),
        },
        "independent_graph_checks": graph_checks,
        "independent_inventory_checks": inventory_checks,
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_calculation_module": False,
            "recomputes_graph_reference_closure_and_topological_order": True,
            "recomputes_node_ledger_hash": True,
            "recomputes_component_inventory": True,
            "recomputes_Minkowski_sparse_hash": True,
            "audits_form_separation_and_claim_ceiling": True,
        },
        "accepted_results": (
            [
                "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE",
                "OFF_SHELL_FORM_COMPLETE",
                "ON_SHELL_REDUCTION_COMPLETE",
                "GAUGE_COMPATIBLE_FORM_COMPLETE",
                "MINKOWSKI_SPECIALIZATION_REPRODUCED",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "EXACT_GENERIC_FROZEN_COMPANION_OPERATOR",
            "GENERIC_CHARACTERISTIC_ROOT_ASYMPTOTICS",
            "CONSTRAINT_TANGENT_PROJECTOR",
            "GENERIC_FINITE_SOBOLEV_LOSS",
            "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
            "QUASILINEAR_OR_LOCAL_WELL_POSEDNESS",
            "QUADRATIC_GRAVITY_PHYSICAL_VIABILITY",
        ],
        "authority_rotation": {
            "stage_2_result_accepted": accepted,
            "stage_3_exact_companion_operator_authorized": accepted,
            "stage_4_constraint_quotient_authorized": False,
            "stage_5_propagator_growth_authorized": False,
            "subsidiary_scientific_target_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
        ),
        "terminal_result": "PASSED" if accepted else "BLOCKED",
        "verdict": (
            "ACCEPT_COMPONENT_EXPANDED_GENERIC_BACKGROUND_LINEARIZATION_"
            "AUTHORIZE_BOUNDED_STAGE_3_ONLY"
            if accepted
            else "BLOCK_COMPONENT_EXPANSION_EXIT_TO_ROLE_GATE"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity strict-harmonic component-expanded generic-"
            "background linearization v1 result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
