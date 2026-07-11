from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-10T00:00:00Z"
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-MULTI-"
    "BACKGROUND-ROBUSTNESS-v0"
)
PACKET_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_GUARDRAIL_PACKET_v0"
)
PACKET_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_GUARDRAIL_PACKET_20260710_v0"
)
PREPARATION_TARGET = (
    "prepare_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_guardrail_packet"
)
EXECUTION_TARGET = (
    "execute_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_v0"
)
EXECUTION_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_multi_background_"
    "robustness_calculation_execution"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_v0_result"
)
REVIEW_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_multi_background_"
    "robustness_calculation_result_review"
)
EVIDENCE_FAILURE_TARGET = (
    "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_v0_evidence_incompatibility"
)
REPRODUCIBILITY_FAILURE_TARGET = (
    "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_v0_reproducibility_mismatch"
)
UNIT_LEDGER_TARGET = "prepare_pillar_seam_unit_mapping_ledger_guardrail_packet"

GUARDRAIL_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_GUARDRAIL_PACKET_PREPARED_AUTHORIZES_BOUNDED_FOUR_"
    "BACKGROUND_EVIDENCE_SYNTHESIS_ONLY"
)
GUARDRAIL_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_GUARDRAIL_PACKET_PREPARED_LEVEL3_CLOSED_FAMILY_FIXED_"
    "BACKGROUND_SYNTHESIS_ONLY_NO_NEW_PDE_SOLVE_NO_GENERAL_THEOREM_NO_"
    "PILLAR_SOURCE_BIANCHI_SEAM_OR_MASTER_ACTION_PROMOTION"
)

GUARDRAIL_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "MULTI_BACKGROUND_ROBUSTNESS_GUARDRAIL_PACKET_20260710_v0.json"
)
GUARDRAIL_REPORT_PATH = REPO_ROOT / GUARDRAIL_REPORT_RELATIVE_PATH
COMPENDIUM_RELATIVE_PATH = (
    "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)
COMPENDIUM_SHA256 = (
    "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
)

FLAT_EQUATION_ID = "EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0"
COVARIANT_EQUATION_ID = (
    "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"
)
EQUATION_SURFACE_STATUS = "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"


def _artifacts(
    *,
    guardrail: tuple[str, str],
    script: tuple[str, str],
    result: tuple[str, str],
    manifest: tuple[str, str],
    execution_report: tuple[str, str],
    review: tuple[str, str],
) -> list[dict[str, str]]:
    return [
        {"artifact_role": role, "path": item[0], "sha256": item[1]}
        for role, item in (
            ("guardrail", guardrail),
            ("calculation_script", script),
            ("calculation_result", result),
            ("calculation_manifest", manifest),
            ("execution_report", execution_report),
            ("independent_review", review),
        )
    ]


SOURCE_CHAINS: list[dict[str, Any]] = [
    {
        "chain_id": "minkowski_1plus1",
        "label": "1+1 Minkowski Cartesian baseline",
        "artifacts": _artifacts(
            guardrail=(
                "formal/docs/release/SCALAR_QFT_GR_SOURCE_CONTRACT_FLAT_LIMIT_"
                "PRETEST_GUARDRAIL_PACKET_20260709_v0.json",
                "a1f29ff370431de8ca1d4e977e00d659a70353ae142472121ea9f44128f07da5",
            ),
            script=(
                "formal/python/toe/calculations/"
                "calc_scalar_stress_energy_divergence_identity_minkowski.py",
                "0eaa19affa8a74084444247c9a04b6997b632490b5411bf436fc3461028547eb",
            ),
            result=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
                "MINKOWSKI-v0.json",
                "c93f2324c735bf2a06ba9a83c3fc022be87b7d00fb5bf2010b8010c2715f480e",
            ),
            manifest=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-"
                "MINKOWSKI-MANIFEST-v0.json",
                "7e2eee401b84c4a8c8dd20c8d54eb6bbba9f16b4e832d53bff6bd7612cd53605",
            ),
            execution_report=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_"
                "MINKOWSKI_CALCULATION_EXECUTION_20260709_v0.json",
                "f1a6b0de45a830b9146cc06b3dbf086ab9bf95f53ae55a5bb80e969df9d53f3f",
            ),
            review=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_"
                "MINKOWSKI_CALCULATION_RESULT_REVIEW_20260709_v0.json",
                "6111a78b0c1ae2ee1170dcbed5ef524ada7c2a720714180808345cffc5b5e916",
            ),
        ),
        "review_status": "accepted_scoped_e_repro",
        "equation_mapping": {
            "source_equation_id": FLAT_EQUATION_ID,
            "family_role": "flat_specialization_bridge",
            "covariant_equation_id": COVARIANT_EQUATION_ID,
            "canonical_row_replaced": False,
        },
        "spacetime_dimension": 2,
        "divergence_component_count": 2,
        "geometry_class": "cartesian_flat_trivial_connection",
        "connection_class": "zero_connection",
        "curvature_class": "zero_curvature",
        "grid_schedule": [64, 128, 256, 512],
        "grid_meaning": "N spatial points",
        "upstream_decision_count": 4,
        "review_target": (
            "review_calc_scalar_stress_energy_divergence_identity_minkowski_"
            "v0_result"
        ),
        "upstream_gate_ids": [
            "exact_coefficient_error_at_most_1e_12",
            "finest_combined_off_shell_relative_error_at_most_2_percent",
            "finest_off_shell_divergence_over_100_times_on_shell",
            "two_finest_convergence_order_at_least_1_8",
        ],
        "profile_coverage": {
            "on_shell": "legacy_on_shell_spatial_wave",
            "off_shell_x": "legacy_off_shell_spatial_wave",
            "off_shell_y": "not_applicable_no_y_coordinate",
            "applicable_divergence_components": ["nu_0", "nu_1"],
        },
        "comparable_profiles": [
            {
                "profile_row_id": "minkowski_off_shell",
                "p_min": 1.997914114431356,
                "off_shell_relative_identity_error": 0.0035695975114978873,
            }
        ],
        "on_shell_policy": {
            "policy_id": "legacy_off_to_on_separation",
            "relative_error_against_zero_allowed": False,
        },
        "flat_limit_role": "cartesian_baseline_not_a_recovery_test",
        "fresh_subprocess_review_status": "not_recorded_in_legacy_review",
    },
    {
        "chain_id": "conformal_connection_1plus1",
        "label": "1+1 locally flat conformal nontrivial connection",
        "artifacts": _artifacts(
            guardrail=(
                "formal/docs/release/BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_"
                "CONTRACT_RETEST_GUARDRAIL_PACKET_20260709_v0.json",
                "0e16434fca7015b8f2f1c5096050dc05d75904ec34f6cba38c63e33227679f63",
            ),
            script=(
                "formal/python/toe/calculations/"
                "calc_scalar_stress_energy_covariant_divergence_identity_"
                "conformal_background.py",
                "5ecc11be6538a9f266a671bff92e2e143d592c7426e89033a2185374420ae399",
            ),
            result=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
                "IDENTITY-CONFORMAL-BACKGROUND-v0.json",
                "1141870b5a83289a7fc36b32a5375f2a48c96070e15b87c05f17ecfa88e62922",
            ),
            manifest=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
                "IDENTITY-CONFORMAL-BACKGROUND-MANIFEST-v0.json",
                "06e609823aea3237d32136f450005458d27f6b985f07f910fd3d37be321c6b79",
            ),
            execution_report=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_CONFORMAL_BACKGROUND_CALCULATION_EXECUTION_"
                "20260709_v0.json",
                "38746a5089013c5d0044962318409c072b81defd0b54e680f7aedfcbcee5e4b9",
            ),
            review=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_CONFORMAL_BACKGROUND_CALCULATION_RESULT_REVIEW_"
                "20260709_v0.json",
                "752c4f92521e55ca125024ea0b5956838ac32230dcee5356f6e2a5ed2176c0df",
            ),
        ),
        "review_status": "accepted_scoped_e_repro",
        "equation_mapping": {
            "source_equation_id": COVARIANT_EQUATION_ID,
            "family_role": "canonical_covariant_identity_evidence",
            "canonical_row_replaced": False,
        },
        "spacetime_dimension": 2,
        "divergence_component_count": 2,
        "geometry_class": "locally_flat_nontrivial_connection",
        "connection_class": "nonzero_connection",
        "curvature_class": "zero_curvature",
        "grid_schedule": [64, 128, 256, 512],
        "grid_meaning": "N spatial points",
        "upstream_decision_count": 6,
        "review_target": (
            "review_calc_scalar_stress_energy_covariant_divergence_identity_"
            "conformal_background_v0_result"
        ),
        "upstream_gate_ids": [
            "exact_coefficient_error_at_most_1e_12",
            "finest_combined_off_shell_relative_error_at_most_2_percent",
            "finest_off_shell_divergence_over_100_times_on_shell",
            "flat_limit_discrepancy_at_most_1e_12",
            "metric_compatibility_error_at_most_1e_12",
            "two_finest_convergence_order_at_least_1_8",
        ],
        "profile_coverage": {
            "on_shell": "on_shell_spatial_wave",
            "off_shell_x": "off_shell_spatial_wave",
            "off_shell_y": "not_applicable_no_y_coordinate",
            "applicable_divergence_components": ["nu_eta", "nu_x"],
        },
        "comparable_profiles": [
            {
                "profile_row_id": "conformal_off_shell",
                "p_min": 1.9979141144313803,
                "off_shell_relative_identity_error": 0.004010933857743127,
            }
        ],
        "on_shell_policy": {
            "policy_id": "legacy_off_to_on_separation",
            "relative_error_against_zero_allowed": False,
        },
        "flat_limit_role": "source_local_flat_limit_recovery_passed",
        "fresh_subprocess_review_status": "not_recorded_in_legacy_review",
    },
    {
        "chain_id": "de_sitter_1plus1",
        "label": "fixed 1+1 de Sitter constant curvature",
        "artifacts": _artifacts(
            guardrail=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_NONZERO_CURVATURE_BACKGROUND_GUARDRAIL_PACKET_"
                "20260709_v0.json",
                "3670bfaa98876b32e95f5ff7406546a41aa691f937fe738fee6e3ab36a399191",
            ),
            script=(
                "formal/python/toe/calculations/"
                "calc_scalar_stress_energy_covariant_divergence_identity_"
                "nonzero_curvature_background.py",
                "253632cc6773d242a76db26befde13dc2578a2950c097a8c628b8e061ffdbd03",
            ),
            result=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
                "IDENTITY-NONZERO-CURVATURE-BACKGROUND-v0.json",
                "4d0d04421c8b0d310f0caa73c4da3755f2afa91a4043bab9f96011c9b03ecf4f",
            ),
            manifest=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
                "IDENTITY-NONZERO-CURVATURE-BACKGROUND-MANIFEST-v0.json",
                "46e752fd0a8571fd06dd0f1f9a7046f12a43413761ea39a3cb904b959a4a6827",
            ),
            execution_report=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_NONZERO_CURVATURE_BACKGROUND_CALCULATION_EXECUTION_"
                "20260709_v0.json",
                "21068eaff2b509401afb635e4f7bce4eb409edb8a5cff6dfe4bea7dfe7a3d2c8",
            ),
            review=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_NONZERO_CURVATURE_BACKGROUND_CALCULATION_RESULT_"
                "REVIEW_20260709_v0.json",
                "538ba6db4e42cdcbaf5f109e3e4beb4c79b0e740db134d04d7293ef1a05d5702",
            ),
        ),
        "review_status": "accepted_scoped_e_repro",
        "equation_mapping": {
            "source_equation_id": COVARIANT_EQUATION_ID,
            "family_role": "canonical_covariant_identity_evidence",
            "canonical_row_replaced": False,
        },
        "spacetime_dimension": 2,
        "divergence_component_count": 2,
        "geometry_class": "constant_nonzero_curvature_de_sitter",
        "connection_class": "nonzero_connection",
        "curvature_class": "constant_nonzero_curvature",
        "grid_schedule": [64, 128, 256, 512],
        "grid_meaning": "N spatial points",
        "upstream_decision_count": 11,
        "review_target": (
            "review_calc_scalar_stress_energy_covariant_divergence_identity_"
            "nonzero_curvature_background_v0_result"
        ),
        "upstream_gate_ids": [
            "absolute_scalar_curvature_at_least_0_05",
            "curvature_omission_discrepancy_at_least_0_04",
            "curvature_route_discrepancy_at_most_1e_12",
            "exact_coefficient_error_at_most_1e_12",
            "finest_combined_off_shell_relative_error_at_most_2_percent",
            "finest_off_shell_divergence_over_100_times_on_shell",
            "flat_limit_discrepancy_at_most_1e_12",
            "inconsistent_frozen_connection_error_ratio_at_least_50",
            "metric_compatibility_error_at_most_1e_12",
            "naive_partial_divergence_error_ratio_at_least_100",
            "two_finest_convergence_order_at_least_1_8",
        ],
        "profile_coverage": {
            "on_shell": "on_shell_spatial_wave",
            "off_shell_x": "off_shell_spatial_wave",
            "off_shell_y": "not_applicable_no_y_coordinate",
            "applicable_divergence_components": ["nu_eta", "nu_x"],
        },
        "comparable_profiles": [
            {
                "profile_row_id": "de_sitter_off_shell",
                "p_min": 1.9979141144314259,
                "off_shell_relative_identity_error": 0.004010933857742557,
            }
        ],
        "on_shell_policy": {
            "policy_id": "legacy_off_to_on_separation",
            "relative_error_against_zero_allowed": False,
        },
        "flat_limit_role": "source_local_flat_limit_recovery_passed",
        "fresh_subprocess_review_status": "not_recorded_in_legacy_review",
    },
    {
        "chain_id": "warped_2plus1",
        "label": "fixed 2+1 warped spatially varying signed curvature",
        "artifacts": _artifacts(
            guardrail=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_"
                "PACKET_20260709_v1.json",
                "e6ce9dfb08364e3fa3a0a3895a3d1b16635348ab2fc7b0490f0b3b6e04db6b96",
            ),
            script=(
                "formal/python/toe/calculations/"
                "calc_scalar_stress_energy_covariant_divergence_identity_"
                "higher_dimensional_curved_background.py",
                "5d43b770a47ec86ccf8a0e09a68d4c1aebf454daea9c471434d288700f57de53",
            ),
            result=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
                "IDENTITY-HIGHER-DIMENSIONAL-CURVED-BACKGROUND-v0.json",
                "755e39e4672ad68e2fbf142d0e2bc9140abb80988e4a330ec3a5fd4ddca859ce",
            ),
            manifest=(
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
                "IDENTITY-HIGHER-DIMENSIONAL-CURVED-BACKGROUND-MANIFEST-v0.json",
                "12791f7844d1c48ea81c647e5d8ee65e32b264592b0101eed875afc7a9d8e5f3",
            ),
            execution_report=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_"
                "EXECUTION_20260709_v0.json",
                "e502995f084bb9d7cdcce8141f7c54fce60026660a3c94f393cf2633f0f22dd2",
            ),
            review=(
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_"
                "RESULT_REVIEW_20260709_v0.json",
                "2bd90958b5c85f255162bfa7f061e8061250443c3c369aaa33bf12ec2077c3e7",
            ),
        ),
        "review_status": "accepted_level_3_scoped_e_repro",
        "equation_mapping": {
            "source_equation_id": COVARIANT_EQUATION_ID,
            "family_role": "canonical_covariant_identity_evidence",
            "canonical_row_replaced": False,
        },
        "spacetime_dimension": 3,
        "divergence_component_count": 3,
        "geometry_class": "spatially_varying_signed_curvature_warped",
        "connection_class": "nonzero_connection",
        "curvature_class": "spatially_varying_signed_curvature_with_zero_crossings",
        "grid_schedule": [32, 64, 128, 256],
        "grid_meaning": "N x N spatial points",
        "upstream_decision_count": 16,
        "review_target": (
            "review_calc_scalar_stress_energy_covariant_divergence_identity_"
            "higher_dimensional_curved_background_v0_result"
        ),
        "upstream_gate_ids": [
            "maximum_analytic_profile_residual_reference_error",
            "maximum_curvature_route_absolute_discrepancy",
            "maximum_finest_on_shell_combined_absolute_divergence_error",
            "maximum_finest_x_mode_combined_relative_identity_error",
            "maximum_finest_y_mode_combined_relative_identity_error",
            "maximum_flat_limit_absolute_discrepancy",
            "maximum_metric_compatibility_absolute_error",
            "minimum_curvature_peak_absolute_value",
            "minimum_curvature_peak_to_peak_variation",
            "minimum_flat_geometry_substitution_normalized_discrepancy",
            "minimum_incorrect_y_inverse_metric_normalized_discrepancy",
            "minimum_naive_partial_divergence_error_ratio",
            "minimum_omitted_tensor_index_term_error_ratio",
            "minimum_omitted_volume_trace_term_error_ratio",
            "minimum_two_finest_x_mode_convergence_order",
            "minimum_two_finest_y_mode_convergence_order",
        ],
        "profile_coverage": {
            "on_shell": "exact_on_shell_temporal_mode",
            "off_shell_x": "off_shell_x_mode",
            "off_shell_y": "off_shell_y_mode",
            "applicable_divergence_components": ["nu_t", "nu_x", "nu_y"],
        },
        "comparable_profiles": [
            {
                "profile_row_id": "warped_x_off_shell",
                "p_min": 1.9916550282637009,
                "off_shell_relative_identity_error": 0.0037615209464743715,
            },
            {
                "profile_row_id": "warped_y_off_shell",
                "p_min": 1.9916554104408082,
                "off_shell_relative_identity_error": 0.002490250625003484,
            },
        ],
        "on_shell_policy": {
            "policy_id": "exact_zero_absolute_divergence",
            "maximum_absolute_divergence": 1e-11,
            "relative_error_against_zero_allowed": False,
        },
        "flat_limit_role": "source_local_flat_limit_recovery_passed",
        "fresh_subprocess_review_status": "two_fresh_subprocesses_matched",
    },
]


CONTROL_INSTANCES = [
    ("minkowski_off_shell_nonconservation", "minkowski_1plus1", "off_shell_nonconservation"),
    ("conformal_naive_partial", "conformal_connection_1plus1", "naive_partial_divergence"),
    ("de_sitter_naive_partial", "de_sitter_1plus1", "naive_partial_divergence"),
    ("de_sitter_frozen_connection", "de_sitter_1plus1", "inconsistent_connection"),
    ("de_sitter_curvature_omission", "de_sitter_1plus1", "curvature_derivative_omission"),
    ("warped_naive_partial", "warped_2plus1", "naive_partial_divergence"),
    ("warped_omit_tensor_index", "warped_2plus1", "omitted_tensor_index_connection"),
    ("warped_omit_volume_trace", "warped_2plus1", "omitted_volume_trace_connection"),
    ("warped_flat_substitution", "warped_2plus1", "flat_geometry_substitution"),
    ("warped_wrong_inverse_metric", "warped_2plus1", "incorrect_inverse_metric_factor"),
]
CONTROL_MECHANISMS = sorted({item[2] for item in CONTROL_INSTANCES})


LOCAL_CHECK_LEDGER = [
    {
        "chain_id": "minkowski_1plus1",
        "analytic_reference": "applicable_upstream_gate",
        "metric_compatibility": "not_applicable_exact_cartesian_metric",
        "curvature_route": "not_applicable_flat_baseline",
        "patch_or_geometry_safety": "not_applicable_global_cartesian_chart",
        "flat_limit": "baseline_not_recovery_test",
        "on_off_shell_witness": "applicable_upstream_gate",
    },
    {
        "chain_id": "conformal_connection_1plus1",
        "analytic_reference": "applicable_upstream_gate",
        "metric_compatibility": "applicable_upstream_gate",
        "curvature_route": "not_applicable_locally_flat_classification",
        "patch_or_geometry_safety": "applicable_reviewed_background_classification",
        "flat_limit": "applicable_upstream_gate",
        "on_off_shell_witness": "applicable_upstream_gate",
    },
    {
        "chain_id": "de_sitter_1plus1",
        "analytic_reference": "applicable_upstream_gate",
        "metric_compatibility": "applicable_upstream_gate",
        "curvature_route": "applicable_upstream_gates",
        "patch_or_geometry_safety": "applicable_reviewed_patch_domain_safety",
        "flat_limit": "applicable_upstream_gate",
        "on_off_shell_witness": "applicable_upstream_gate",
    },
    {
        "chain_id": "warped_2plus1",
        "analytic_reference": "applicable_upstream_gate",
        "metric_compatibility": "applicable_upstream_gate",
        "curvature_route": "applicable_upstream_gates",
        "patch_or_geometry_safety": "applicable_reviewed_determinant_safety",
        "flat_limit": "applicable_upstream_gate",
        "on_off_shell_witness": "applicable_upstream_gates",
    },
]


DECISIONS = [
    (1, "exact_twenty_four_artifact_chain_integrity", "exactly 4 chains and 24 bound artifacts match paths, hashes, schemas, canonical bytes where applicable, and internal links"),
    (2, "four_level3_review_acceptances", "exactly 4 independent reviews accept E-REPRO at claim ceiling 3"),
    (3, "identity_and_flat_specialization_mapping", "the shared covariant identity/sign convention matches and Minkowski remains a typed zero-connection flat specialization"),
    (4, "four_geometry_class_coverage", "the exact four frozen geometry classes are present once each"),
    (5, "dimension_and_component_coverage", "spacetime dimensions and divergence-component counts are both exactly {2,3}"),
    (6, "connection_class_coverage", "zero and nonzero connection classes are both present"),
    (7, "curvature_class_coverage", "zero, constant nonzero, and varying signed curvature with zero crossings are present"),
    (8, "profile_and_component_role_coverage", "on-shell, off-shell x, off-shell y, and every locally applicable component role are present"),
    (9, "all_thirty_seven_upstream_decisions_pass", "source decision counts are exactly 4+6+11+16 and every decision passes without masking"),
    (10, "family_minimum_convergence_order", "exactly five comparable p_min rows exist and their family minimum is at least 1.8"),
    (11, "family_maximum_off_shell_relative_error", "exactly five normalized off-shell rows exist and their family maximum is at most 0.02"),
    (12, "source_local_on_shell_policies", "all source-local on-shell policies pass and no relative error against an exact zero is formed"),
    (13, "applicability_typed_local_checks", "all locally applicable analytic, metric, curvature, patch, flat-limit, and witness checks pass; inapplicable fields remain typed null/not_applicable"),
    (14, "ten_control_instances_eight_mechanisms", "exactly ten detected source control instances cover the exact eight frozen mechanisms with no combined masking"),
    (15, "comparison_policy_no_invalid_pooling", "only convergence order and within-background dimensionless off-shell error form family envelopes"),
    (16, "lifecycle_claim_and_unit_ledger_boundaries", "candidate Level 3 review lifecycle and all nonclaims hold while the unit ledger remains a non-live hard gate"),
]


SYNTHESIS_TAMPER_CONTROLS = [
    ("omitted_background", "remove one chain", "four_geometry_class_coverage"),
    ("swapped_chain_artifacts", "swap artifacts between two chain labels", "exact_twenty_four_artifact_chain_integrity"),
    ("masked_upstream_failure", "flip one upstream decision false while retaining a passing family average", "all_thirty_seven_upstream_decisions_pass"),
    ("inapplicable_zero_fill", "replace not_applicable with numeric zero/pass", "applicability_typed_local_checks"),
    ("on_shell_relative_error_injection", "inject a floor-divided relative error against an exact-zero reference", "source_local_on_shell_policies"),
    ("raw_absolute_error_substitution", "substitute raw absolute divergence for a normalized off-shell ratio", "comparison_policy_no_invalid_pooling"),
    ("removed_control_instance", "remove one control instance while leaving a combined pass flag true", "ten_control_instances_eight_mechanisms"),
    ("input_hash_tamper", "alter one bound source hash", "exact_twenty_four_artifact_chain_integrity"),
    ("review_hash_tamper", "alter one accepted-review hash", "exact_twenty_four_artifact_chain_integrity"),
    ("result_hash_tamper", "alter one calculation-result hash", "exact_twenty_four_artifact_chain_integrity"),
    ("nonfinite_injection", "inject NaN or infinity", "exact_twenty_four_artifact_chain_integrity"),
    ("degeneracy_language_leak", "import 1+1 Einstein-degeneracy language into the 2+1 row", "lifecycle_claim_and_unit_ledger_boundaries"),
    ("collapsed_curvature_classes", "merge constant and spatially varying curvature classes", "curvature_class_coverage"),
    ("forbidden_claim_promotion", "set any pillar/source/Bianchi/seam/CCFT/C_k dynamics/master-action promotion true", "lifecycle_claim_and_unit_ledger_boundaries"),
]


def report_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _reject_nonfinite_constant(value: str) -> None:
    raise ValueError(f"nonfinite JSON constant is forbidden: {value}")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key is forbidden: {key}")
        result[key] = value
    return result


def _load_strict_json(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError(f"JSON BOM is forbidden: {path}")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"JSON is not UTF-8: {path}") from exc
    payload = json.loads(
        text,
        parse_constant=_reject_nonfinite_constant,
        object_pairs_hook=_reject_duplicate_keys,
    )
    if not isinstance(payload, dict):
        raise ValueError(f"JSON root is not an object: {path}")
    return payload


def _artifact_by_role(chain: dict[str, Any], role: str) -> dict[str, str]:
    matches = [
        artifact
        for artifact in chain["artifacts"]
        if artifact["artifact_role"] == role
    ]
    if len(matches) != 1:
        raise ValueError(
            f"chain {chain['chain_id']} must bind exactly one {role} artifact"
        )
    return matches[0]


def build_guardrail_payload() -> dict[str, Any]:
    source_chains = copy.deepcopy(SOURCE_CHAINS)
    comparable_rows = [
        row
        for chain in source_chains
        for row in chain["comparable_profiles"]
    ]
    upstream_gate_inventory = [
        {
            "chain_id": chain["chain_id"],
            "qualified_gate_id": f"{chain['chain_id']}::{gate_id}",
            "source_gate_id": gate_id,
            "must_pass_individually": True,
        }
        for chain in source_chains
        for gate_id in chain["upstream_gate_ids"]
    ]
    source_link_contract = [
        {
            "chain_id": chain["chain_id"],
            "result_review_target": chain["review_target"],
            "review_consumed_target": chain["review_target"],
            "result_sha256": next(
                artifact["sha256"]
                for artifact in chain["artifacts"]
                if artifact["artifact_role"] == "calculation_result"
            ),
            "review_must_bind_result_hash": True,
            "review_must_accept_level_3_e_repro": True,
        }
        for chain in source_chains
    ]
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "packet_id": PACKET_ID,
        "calculation_id": CALCULATION_ID,
        "status": "prepared_authorizes_execution_only",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": PREPARATION_TARGET,
        "consumed_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_multi_"
            "background_robustness_guardrail_packet"
        ),
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": EXECUTION_TARGET_KIND,
        "future_review_target": REVIEW_TARGET,
        "future_review_target_kind": REVIEW_TARGET_KIND,
        "failure_targets": {
            "execution_evidence_incompatibility": EVIDENCE_FAILURE_TARGET,
            "review_reproducibility_mismatch": REPRODUCIBILITY_FAILURE_TARGET,
        },
        "packet_result": GUARDRAIL_OUTCOME,
        "strict_packet_result": GUARDRAIL_STRICT_OUTCOME,
        "question": (
            "Do the four enumerated, previously reviewed scalar identity chains "
            "form a coherent bounded Level 3 robustness pattern without "
            "pooling incommensurate diagnostics or promoting the claim?"
        ),
        "synthesis_classification": {
            "kind": "closed_enumerated_family_evidence_synthesis",
            "new_pde_calculation": False,
            "statistical_sample": False,
            "backgrounds_randomly_sampled": False,
            "backgrounds_selected_sequentially_before_synthesis": True,
            "implementation_lineage_independent": False,
            "arbitrary_background_generalization_allowed": False,
        },
        "source_chain_count": 4,
        "bound_artifact_count": 24,
        "source_chains": source_chains,
        "source_review_result_link_contract": source_link_contract,
        "equation_compendium_boundary": {
            "path": COMPENDIUM_RELATIVE_PATH,
            "sha256": COMPENDIUM_SHA256,
            "flat_specialization_equation_id": FLAT_EQUATION_ID,
            "canonical_covariant_equation_id": COVARIANT_EQUATION_ID,
            "canonical_covariant_equation_status": EQUATION_SURFACE_STATUS,
            "canonical_source_cell_must_remain_unchanged": True,
            "equation_row_promotion_authorized": False,
        },
        "identity_contract": {
            "identity": (
                "nabla_mu T^{mu nu} = (Box_g phi - V'(phi)) "
                "nabla^nu phi"
            ),
            "minkowski_role": "zero_connection_flat_specialization",
            "massless_specialization_allowed": True,
            "sign_convention_must_match_each_frozen_chain": True,
        },
        "coverage_contract": {
            "chain_ids": [chain["chain_id"] for chain in source_chains],
            "geometry_classes": [chain["geometry_class"] for chain in source_chains],
            "spacetime_dimensions": [2, 3],
            "divergence_component_counts": [2, 3],
            "connection_classes": ["zero_connection", "nonzero_connection"],
            "curvature_classes": [
                "zero_curvature",
                "constant_nonzero_curvature",
                "spatially_varying_signed_curvature_with_zero_crossings",
            ],
            "profile_roles": [
                "exact_on_shell_temporal",
                "off_shell_x_or_legacy_spatial",
                "off_shell_y_warped",
                "all_locally_applicable_divergence_components",
            ],
            "profile_coverage_by_chain": {
                chain["chain_id"]: chain["profile_coverage"]
                for chain in source_chains
            },
            "dimension_language_policy": {
                "legacy_1plus1_Einstein_degeneracy_is_source_local": True,
                "warped_2plus1_two_dimensional_Einstein_degeneracy_not_applicable": True,
                "one_plus_one_degeneracy_must_not_be_imported_into_2plus1": True,
            },
        },
        "upstream_decision_contract": {
            "per_chain_counts": {
                chain["chain_id"]: chain["upstream_decision_count"]
                for chain in source_chains
            },
            "total_count": 37,
            "gate_inventory": upstream_gate_inventory,
            "all_must_pass_individually": True,
            "averaging_or_masking_forbidden": True,
        },
        "comparable_metric_contract": {
            "profile_row_count": 5,
            "profile_rows": comparable_rows,
            "family_minimum_p_min_reference": min(
                row["p_min"] for row in comparable_rows
            ),
            "minimum_allowed_family_p_min": 1.8,
            "family_maximum_off_shell_relative_error_reference": max(
                row["off_shell_relative_identity_error"]
                for row in comparable_rows
            ),
            "maximum_allowed_family_off_shell_relative_error": 0.02,
            "normalization": (
                "RMS(divergence-analytic_RHS)/"
                "max(RMS(analytic_RHS),epsilon_norm)"
            ),
            "epsilon_norm": 1e-14,
            "norm_name": "uniform_unweighted_coordinate_grid_component_rms",
            "coordinate_invariant": False,
            "volume_weighted": False,
            "use_as_threshold_envelope_not_performance_ranking": True,
        },
        "source_local_policy_contract": {
            "on_shell_policies": {
                chain["chain_id"]: chain["on_shell_policy"]
                for chain in source_chains
            },
            "flat_limit_roles": {
                chain["chain_id"]: chain["flat_limit_role"]
                for chain in source_chains
            },
            "fresh_subprocess_review_status": {
                chain["chain_id"]: chain["fresh_subprocess_review_status"]
                for chain in source_chains
            },
            "not_applicable_representation": "null_with_not_applicable_status",
            "zero_fill_for_not_applicable_forbidden": True,
            "on_shell_relative_error_against_exact_zero_forbidden": True,
        },
        "applicability_typed_local_check_ledger": copy.deepcopy(
            LOCAL_CHECK_LEDGER
        ),
        "control_contract": {
            "instance_count": len(CONTROL_INSTANCES),
            "mechanism_count": len(CONTROL_MECHANISMS),
            "instances": [
                {
                    "control_instance_id": item[0],
                    "chain_id": item[1],
                    "mechanism_class": item[2],
                }
                for item in CONTROL_INSTANCES
            ],
            "mechanism_classes": CONTROL_MECHANISMS,
            "conformal_naive_partial_is_diagnostic_without_new_threshold": True,
            "ratios_are_source_local_and_must_not_be_ranked": True,
            "combined_status_is_logical_and_only": True,
        },
        "comparison_policy": {
            "family_envelopes_allowed": [
                "dimensionless_second_order_convergence_p_min",
                "within_background_dimensionless_off_shell_relative_identity_error",
            ],
            "cross_background_pooling_forbidden": [
                "absolute_divergence_error",
                "curvature_magnitude",
                "curvature_route_absolute_error",
                "grid_N",
                "connection_component_count",
                "analytic_residual_coefficient",
                "negative_control_ratio_or_discrepancy",
                "raw_timing_or_cost",
            ],
            "two_plus_one_grid_N_means_N_by_N": True,
            "source_grid_schedules_must_remain_tagged": True,
            "physical_performance_ranking_allowed": False,
        },
        "success_criteria": {
            "all_decisions_required": True,
            "exact_source_chain_count": 4,
            "exact_bound_artifact_count": 24,
            "exact_accepted_review_count": 4,
            "exact_upstream_decision_count": 37,
            "exact_comparable_profile_row_count": 5,
            "minimum_family_convergence_order": 1.8,
            "maximum_family_off_shell_relative_error": 0.02,
            "exact_control_instance_count": 10,
            "exact_control_mechanism_count": 8,
            "exact_geometry_class_count": 4,
            "exact_spacetime_dimension_count": 2,
            "exact_divergence_component_count_class_count": 2,
        },
        "frozen_decision_count": len(DECISIONS),
        "frozen_decisions": [
            {
                "decision_number": item[0],
                "decision_id": item[1],
                "requirement": item[2],
            }
            for item in DECISIONS
        ],
        "synthesis_tamper_control_count": len(SYNTHESIS_TAMPER_CONTROLS),
        "synthesis_tamper_controls": [
            {
                "control_id": item[0],
                "exact_mutation": item[1],
                "expected_failed_decision_id": item[2],
                "must_fail_individually": True,
            }
            for item in SYNTHESIS_TAMPER_CONTROLS
        ],
        "execution_artifact_contract": {
            "must_include": [
                "guardrail identity and hash",
                "four six-artifact chain records",
                "four typed background comparison rows",
                "five convergence rows",
                "five normalized off-shell-error rows",
                "thirty-seven source-decision inventory rows",
                "four source-local on-shell policy rows",
                "applicability-tagged local-check rows",
                "ten control-instance rows and eight-mechanism coverage",
                "sixteen decision rows",
                "sampling, coordinate-norm, lineage, and claim limitations",
            ],
            "must_not_embed": "full upstream numerical row sets",
            "result_path": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-MULTI-BACKGROUND-ROBUSTNESS-v0.json"
            ),
            "manifest_path": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-MULTI-BACKGROUND-ROBUSTNESS-MANIFEST-v0.json"
            ),
            "execution_report_path": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_MULTI_BACKGROUND_ROBUSTNESS_"
                "CALCULATION_EXECUTION_20260710_v0.json"
            ),
            "review_report_path": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_MULTI_BACKGROUND_ROBUSTNESS_"
                "CALCULATION_RESULT_REVIEW_20260710_v0.json"
            ),
            "temporary_paths_wall_clock_and_random_values_forbidden": True,
        },
        "independent_review_contract": {
            "rederive_every_summary_from_immutable_inputs": True,
            "fresh_synthesis_subprocess_count": 2,
            "byte_identical_result_manifest_and_execution_report_required": True,
            "accepted_upstream_artifacts_must_not_be_rewritten": True,
            "review_failure_target": REPRODUCIBILITY_FAILURE_TARGET,
        },
        "failure_policy": {
            "primary_claim_label": "B-BLOCKED",
            "artifacts_preserved": True,
            "nonzero_exit_required": True,
            "selected_target": EVIDENCE_FAILURE_TARGET,
            "threshold_relaxation_or_family_substitution_forbidden": True,
            "changes_require_new_versioned_guardrail": True,
        },
        "claim_ceiling": {
            "claim_ladder_level": 3,
            "candidate_primary_label": "E-REPRO",
            "execution_status": "candidate_pending_independent_review_only",
            "allowed_after_successful_review": (
                "reproducible robustness across the exact four enumerated "
                "fixed-background evidence chains"
            ),
            "not_a_theorem": True,
            "not_a_statistical_generalization": True,
            "not_implementation_independence": True,
            "not_arbitrary_background_validity": True,
        },
        "boundary": {
            "new_pde_solve_authorized": False,
            "gravity_evolution_claimed": False,
            "einstein_source_compatibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "scalar_qft_pillar_recovery_claimed": False,
            "level_4_or_level_5_claimed": False,
            "quantum_or_renormalized_stress_energy_claimed": False,
            "ccft_resumed": False,
            "C_k_dynamics_claimed": False,
            "C_k_action_embedding_authorized": False,
            "master_action_promoted": False,
            "readiness_refresh_executed": False,
            "unit_ledger_target": UNIT_LEDGER_TARGET,
            "unit_ledger_status": "queued_non_live_hard_gate",
            "unit_ledger_required_before_stronger_claims": True,
        },
        "allowed_operations": [
            "read and hash the exact twenty-four frozen upstream artifacts",
            "strictly parse canonical JSON artifacts and verify internal links",
            "construct the four-row typed comparison matrix",
            "extract the five comparable convergence and relative-error rows",
            "recheck all thirty-seven source decisions without averaging",
            "construct applicability-tagged local-check and control inventories",
            "run every frozen synthesis tamper control separately",
            "write deterministic result, manifest, and execution report artifacts",
        ],
        "forbidden_operations": [
            "solve a new field equation or rerun a fifth background as evidence",
            "modify any accepted upstream artifact",
            "average or rank a forbidden raw cross-background metric",
            "replace an inapplicable field with numeric zero or pass",
            "form a relative error against an exact-zero on-shell reference",
            "promote an equation row, pillar, source, seam, C_k, or master action",
        ],
        "canonical_json_contract": {
            "encoding": "UTF-8 without BOM",
            "newline": "LF",
            "object_keys": "sorted",
            "indent": 2,
            "ensure_ascii": True,
            "allow_nan": False,
            "trailing_newline": "exactly one LF",
        },
        "calculation_executed": False,
        "e_repro_claimed_by_guardrail": False,
        "equation_compendium_edited": False,
        "full_ToeFormal_aggregate_run_or_upgraded": False,
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal "
            "aggregate not run / not upgraded"
        ),
    }


def validate_bound_sources(payload: dict[str, Any]) -> None:
    if len(payload["source_chains"]) != 4:
        raise ValueError("expected exactly four source chains")
    artifacts = [
        artifact
        for chain in payload["source_chains"]
        for artifact in chain["artifacts"]
    ]
    if len(artifacts) != 24:
        raise ValueError("expected exactly twenty-four source artifacts")
    for artifact in artifacts:
        path = REPO_ROOT / artifact["path"]
        if not path.is_file() or sha256_path(path) != artifact["sha256"]:
            raise ValueError(f"bound source artifact mismatch: {artifact['path']}")
    if len({artifact["path"] for artifact in artifacts}) != 24:
        raise ValueError("bound source artifact paths must be unique")

    hash_key_by_role = {
        "guardrail": "guardrail_sha256",
        "calculation_script": "script_sha256",
        "calculation_result": "output_sha256",
        "calculation_manifest": "manifest_sha256",
        "execution_report": "execution_report_sha256",
    }
    for chain in payload["source_chains"]:
        result_artifact = _artifact_by_role(chain, "calculation_result")
        review_artifact = _artifact_by_role(chain, "independent_review")
        result = _load_strict_json(REPO_ROOT / result_artifact["path"])
        review = _load_strict_json(REPO_ROOT / review_artifact["path"])

        checks = result.get("threshold_checks")
        if not isinstance(checks, dict):
            raise ValueError(f"missing source gate map: {chain['chain_id']}")
        if set(checks) != set(chain["upstream_gate_ids"]):
            raise ValueError(f"source gate inventory mismatch: {chain['chain_id']}")
        if len(checks) != chain["upstream_decision_count"] or not all(
            value is True for value in checks.values()
        ):
            raise ValueError(f"source gate failure or masking: {chain['chain_id']}")
        if result.get("all_thresholds_passed") is not True:
            raise ValueError(f"source combined gate is not true: {chain['chain_id']}")

        result_review = result.get("result_review")
        if not isinstance(result_review, dict) or result_review != {
            "status": "pending",
            "target": chain["review_target"],
        }:
            raise ValueError(f"result review link mismatch: {chain['chain_id']}")
        if review.get("consumed_target") != chain["review_target"]:
            raise ValueError(f"review consumed-target mismatch: {chain['chain_id']}")
        if review.get("status") != chain["review_status"]:
            raise ValueError(f"review acceptance status mismatch: {chain['chain_id']}")
        claim = review.get("claim")
        verification = review.get("verification")
        if not isinstance(claim, dict) or not isinstance(verification, dict):
            raise ValueError(f"review contract missing: {chain['chain_id']}")
        if (
            claim.get("claim_ceiling_level") != 3
            or claim.get("primary_label") != "E-REPRO"
            or verification.get("accepted") is not True
            or verification.get("primary_claim_label") != "E-REPRO"
            or verification.get("mismatch_codes") != []
        ):
            raise ValueError(f"review is not accepted Level 3: {chain['chain_id']}")

        actual_hashes = verification.get("actual_hashes")
        expected_hashes = verification.get("expected_hashes")
        if not isinstance(actual_hashes, dict) or not isinstance(
            expected_hashes, dict
        ):
            raise ValueError(f"review hash links missing: {chain['chain_id']}")
        for role, hash_key in hash_key_by_role.items():
            expected_sha256 = _artifact_by_role(chain, role)["sha256"]
            if (
                actual_hashes.get(hash_key) != expected_sha256
                or expected_hashes.get(hash_key) != expected_sha256
            ):
                raise ValueError(
                    f"review artifact hash link mismatch: {chain['chain_id']}:{role}"
                )
        if actual_hashes["output_sha256"] != result_artifact["sha256"]:
            raise ValueError(f"review/result hash mismatch: {chain['chain_id']}")

        parameters = result.get("parameters")
        if not isinstance(parameters, dict) or parameters.get(
            "resolutions_N"
        ) != chain["grid_schedule"]:
            raise ValueError(f"source-local grid schedule mismatch: {chain['chain_id']}")
        if chain["chain_id"] == "warped_2plus1":
            reproduction = verification.get("fresh_subprocess_reproduction")
            if (
                not isinstance(reproduction, dict)
                or reproduction.get("run_count") != 2
                or reproduction.get("both_runs_byte_identical") is not True
                or reproduction.get("fresh_runs_match_repository_artifacts")
                is not True
            ):
                raise ValueError("warped fresh-subprocess evidence mismatch")
        elif "fresh_subprocess_reproduction" in verification:
            raise ValueError(
                f"legacy review reproduction strength changed: {chain['chain_id']}"
            )

    compendium = REPO_ROOT / payload["equation_compendium_boundary"]["path"]
    if sha256_path(compendium) != payload["equation_compendium_boundary"]["sha256"]:
        raise ValueError("equation compendium boundary hash mismatch")
    compendium_text = compendium.read_text(encoding="utf-8")
    if FLAT_EQUATION_ID not in compendium_text or COVARIANT_EQUATION_ID not in (
        compendium_text
    ):
        raise ValueError("equation family mapping is absent from the compendium")


def validate_guardrail_payload(payload: dict[str, Any]) -> None:
    if payload != build_guardrail_payload():
        raise ValueError("guardrail payload differs from exact frozen contract")
    if payload["frozen_decision_count"] != 16:
        raise ValueError("guardrail must freeze exactly sixteen decisions")
    if [row["decision_number"] for row in payload["frozen_decisions"]] != list(
        range(1, 17)
    ):
        raise ValueError("guardrail decision numbering differs")
    if len({row["decision_id"] for row in payload["frozen_decisions"]}) != 16:
        raise ValueError("guardrail decision ids are not unique")
    if payload["upstream_decision_contract"]["total_count"] != 37:
        raise ValueError("upstream decision count differs")
    gate_inventory = payload["upstream_decision_contract"]["gate_inventory"]
    if len(gate_inventory) != 37 or len(
        {row["qualified_gate_id"] for row in gate_inventory}
    ) != 37:
        raise ValueError("upstream gate inventory differs")
    if payload["control_contract"]["instance_count"] != 10:
        raise ValueError("control instance count differs")
    if payload["control_contract"]["mechanism_count"] != 8:
        raise ValueError("control mechanism count differs")
    if payload["comparable_metric_contract"]["profile_row_count"] != 5:
        raise ValueError("comparable profile row count differs")
    profile_rows = payload["comparable_metric_contract"]["profile_rows"]
    if payload["comparable_metric_contract"][
        "family_minimum_p_min_reference"
    ] != min(row["p_min"] for row in profile_rows):
        raise ValueError("family convergence envelope differs")
    if payload["comparable_metric_contract"][
        "family_maximum_off_shell_relative_error_reference"
    ] != max(row["off_shell_relative_identity_error"] for row in profile_rows):
        raise ValueError("family relative-error envelope differs")
    if len(payload["applicability_typed_local_check_ledger"]) != 4:
        raise ValueError("applicability ledger differs")
    expected_mechanisms = {
        "off_shell_nonconservation",
        "naive_partial_divergence",
        "inconsistent_connection",
        "curvature_derivative_omission",
        "omitted_tensor_index_connection",
        "omitted_volume_trace_connection",
        "flat_geometry_substitution",
        "incorrect_inverse_metric_factor",
    }
    if set(payload["control_contract"]["mechanism_classes"]) != (
        expected_mechanisms
    ):
        raise ValueError("control mechanism classes differ")
    if payload["selected_next_target"] != EXECUTION_TARGET:
        raise ValueError("guardrail execution target differs")
    if any(payload["boundary"][key] is not False for key in (
        "new_pde_solve_authorized",
        "gravity_evolution_claimed",
        "einstein_source_compatibility_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_seam_admissibility_claimed",
        "qft_gr_seam_closure_claimed",
        "scalar_qft_pillar_recovery_claimed",
        "level_4_or_level_5_claimed",
        "ccft_resumed",
        "C_k_dynamics_claimed",
        "C_k_action_embedding_authorized",
        "master_action_promoted",
    )):
        raise ValueError("guardrail overclaims")
    report_json_bytes(payload)


def write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def guardrail_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the closed-family scalar multi-background robustness guardrail."
        )
    )
    parser.add_argument("--out", type=Path, default=GUARDRAIL_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    validate_bound_sources(payload)
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "artifact_count": payload["bound_artifact_count"],
                "chain_count": payload["source_chain_count"],
                "decision_count": payload["frozen_decision_count"],
                "outcome": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(guardrail_main())
