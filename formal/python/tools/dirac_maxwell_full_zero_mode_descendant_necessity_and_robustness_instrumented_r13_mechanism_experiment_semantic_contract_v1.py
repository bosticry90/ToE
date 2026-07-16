from __future__ import annotations

"""Pure semantic contract for the corrected R13 mechanism freeze (v1).

This module does not load the historical evolution, create output, or expose an
execution entry point.  It freezes three things needed by the corrected packet:

* a non-tautological H_C comparison between two independently sourced paths;
* complete, pre-execution provenance for every H_A--H_D support constant; and
* the deduplicated adversarial contract required by the v0 freeze review.

The six-run v0 matrix and every v0 artifact remain historical inputs.  Nothing
in this module authorizes or performs a simulation.
"""

import math
from collections.abc import Mapping
from typing import Any

import numpy as np


CONTRACT_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_SEMANTIC_CONTRACT_v1"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1.py"
)
DESIGN_REVIEW_V1_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v1.json"
)
FREEZE_V0_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "PACKET-v0.json"
)
FREEZE_REVIEW_V0_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "REVIEW_20260715_v0.json"
)
SOURCE_CATEGORIES: tuple[str, ...] = (
    "ANALYTIC_BOUND",
    "MACHINE_ARITHMETIC",
    "CANONICAL_HISTORY",
    "ACCEPTED_DIAGNOSTIC_EVIDENCE",
    "DESIGN_POLICY",
    "SCHEMA_CONSTANT",
)
UNCOMMITTED_SOURCE_SENTINEL = "WORKTREE_PRE_EXECUTION_NOT_COMMITTED"


# Exactly 23 leaves.  H_A, H_B, and H_D retain the pre-execution v0 values.
# H_C removes gamma_n entirely from mechanism classification.  Its direct-path
# mismatch is scaled by the larger path norm or one requested solver tolerance.
SUPPORT_CONSTANTS_V1: dict[str, dict[str, Any]] = {
    "H_A": {
        "loose_median_kappa_minimum": 1.0e6,
        "severe_step_fraction_minimum": 0.75,
        "directional_log10_contrast_minimum": 1.0,
        "required_postinitial_step_count": 16,
    },
    "H_B": {
        "eligible_longitudinal_block_ids": [
            "THETA_KINEMATIC",
            "P_LONGITUDINAL_MAXWELL",
        ],
        "dominance_share_minimum": 0.50,
        "dominant_step_fraction_minimum": 0.75,
        "median_share_advantage_minimum": 0.20,
        "median_share_ratio_minimum": 2.0,
    },
    "H_C": {
        "relative_path_mismatch_minimum": 0.10,
        "minimum_consecutive_mismatch_steps": 2,
        "loose_to_tight_max_ratio_minimum": 10.0,
        "loose_to_neighbor_max_ratio_minimum": 2.0,
        "required_postinitial_step_count": 16,
        "path_scale_floor_tolerance_multiplier": 1.0,
    },
    "H_D": {
        "minimum_contributing_block_count_per_step": 3,
        "per_block_share_minimum": 0.10,
        "effective_block_count_minimum": 3.0,
        "single_block_share_maximum_exclusive": 0.50,
        "distributed_step_fraction_minimum": 0.75,
        "distributed_fraction_advantage_over_each_reference_minimum": 0.25,
        "linked_structural_series_count": 4,
        "minimum_nondecreasing_increments_per_series": 14,
    },
}


def _provenance(
    hypothesis: str,
    constant_id: str,
    *,
    unit: str,
    source_record_ids: list[str],
    derivation_formula: str,
    rounding_rule: str,
    scientific_meaning: str,
    provenance_class: str = "INHERITED_PREEXECUTION_V0_VALUE",
    source_category: str = "DESIGN_POLICY",
    source_artifact: str = FREEZE_V0_RELATIVE_PATH,
    additional_source_artifacts: list[str] | None = None,
) -> dict[str, Any]:
    if source_category not in SOURCE_CATEGORIES:
        raise ValueError(f"unknown support-constant source category: {source_category}")
    return {
        "hypothesis": hypothesis,
        "constant_id": constant_id,
        "value": SUPPORT_CONSTANTS_V1[hypothesis][constant_id],
        "unit": unit,
        "units": unit,
        "role": "HYPOTHESIS_SUPPORT_CONSTANT",
        "source_category": source_category,
        "source_commit": UNCOMMITTED_SOURCE_SENTINEL,
        "source_artifact": source_artifact,
        "source_artifacts": [source_artifact]
        + list(additional_source_artifacts or []),
        "source_record_ids": list(source_record_ids),
        "derivation_formula": derivation_formula,
        "rounding_rule": rounding_rule,
        "scientific_meaning": scientific_meaning,
        "decision_bearing_or_descriptive": "DECISION_BEARING",
        "provenance_class": provenance_class,
        "nonfuture": True,
        "declared_before_mechanism_execution": True,
        "future_mechanism_outputs_used": False,
        "posthoc_fit_or_point_selection_used": False,
    }


_V0_CONSTANT_ROOT = (
    "/classifier_freeze/support_constants_bound_directly_from_classifier_source"
)
_V0_METRIC_ROOT = "/metric_configuration_template"
_DESIGN_OBLIGATION_ROOT = "/freeze_packet_preparation_obligations"
_HC_REVIEW_FINDING = (
    "/blocking_findings/B_H_C_OPERATOR_MECHANISM_AND_GAMMA_BOUND_UNJUSTIFIED"
)


SUPPORT_CONSTANT_PROVENANCE: tuple[dict[str, Any], ...] = (
    _provenance(
        "H_A",
        "loose_median_kappa_minimum",
        unit="dimensionless cancellation conditioning",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_A/loose_median_kappa_minimum"],
        derivation_formula="10**6; six-decimal-digit cancellation-conditioning boundary",
        rounding_rule="exact base-10 integer power; no rounding",
        scientific_meaning="requires materially severe cancellation in loose R13",
    ),
    _provenance(
        "H_A",
        "severe_step_fraction_minimum",
        unit="fraction of 16 postinitial steps",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_A/severe_step_fraction_minimum"],
        derivation_formula="12/16",
        rounding_rule="exact binary64 representation of 3/4",
        scientific_meaning="requires severe conditioning for at least twelve steps",
    ),
    _provenance(
        "H_A",
        "directional_log10_contrast_minimum",
        unit="base-10 decades",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_A/directional_log10_contrast_minimum"],
        derivation_formula="log10(10)",
        rounding_rule="exact decimal policy value 1.0",
        scientific_meaning="requires at least a one-decade loose/reference contrast",
    ),
    _provenance(
        "H_A",
        "required_postinitial_step_count",
        unit="postinitial steps",
        source_record_ids=[
            f"{_V0_CONSTANT_ROOT}/H_A/required_postinitial_step_count",
            "/exact_run_matrix/common_numerics/accepted_step_count",
        ],
        derivation_formula="T/dt = 0.05/0.003125 = 16",
        rounding_rule="exact integer quotient required",
        scientific_meaning="forbids posthoc omission of time samples",
        source_category="CANONICAL_HISTORY",
    ),
    _provenance(
        "H_B",
        "eligible_longitudinal_block_ids",
        unit="ordered block-ID set",
        source_record_ids=[
            f"{_V0_CONSTANT_ROOT}/H_B/eligible_longitudinal_block_ids",
            "/equation_block_registry",
        ],
        derivation_formula="ordered intersection of the eight packed blocks with the longitudinal theta/p subsystem",
        rounding_rule="not applicable; exact ordered UTF-8 identifiers",
        scientific_meaning="restricts H_B to the two longitudinal equation blocks",
        source_category="SCHEMA_CONSTANT",
    ),
    _provenance(
        "H_B",
        "dominance_share_minimum",
        unit="normalized block-share fraction",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_B/dominance_share_minimum"],
        derivation_formula="1/2",
        rounding_rule="exact binary64 representation",
        scientific_meaning="requires one longitudinal block to carry at least half the normalized defect",
    ),
    _provenance(
        "H_B",
        "dominant_step_fraction_minimum",
        unit="fraction of 16 postinitial steps",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_B/dominant_step_fraction_minimum"],
        derivation_formula="12/16",
        rounding_rule="exact binary64 representation of 3/4",
        scientific_meaning="requires persistent rather than one-step block dominance",
    ),
    _provenance(
        "H_B",
        "median_share_advantage_minimum",
        unit="normalized-share difference",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_B/median_share_advantage_minimum"],
        derivation_formula="1/5",
        rounding_rule="stored as the nearest binary64 value to decimal 0.20",
        scientific_meaning="requires a material absolute loose/reference dominance separation",
    ),
    _provenance(
        "H_B",
        "median_share_ratio_minimum",
        unit="dimensionless ratio",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_B/median_share_ratio_minimum"],
        derivation_formula="2/1",
        rounding_rule="exact binary64 integer ratio",
        scientific_meaning="requires the loose share to be at least twice each reference share",
    ),
    _provenance(
        "H_C",
        "relative_path_mismatch_minimum",
        unit="dimensionless relative L-infinity mismatch",
        source_artifact=FREEZE_REVIEW_V0_RELATIVE_PATH,
        additional_source_artifacts=[DESIGN_REVIEW_V1_RELATIVE_PATH],
        source_record_ids=[_HC_REVIEW_FINDING, _DESIGN_OBLIGATION_ROOT],
        derivation_formula="1/10 of max(||Maxwell_path||_inf, ||continuity_Gauss_path||_inf, solver_tolerance)",
        rounding_rule="stored as the nearest binary64 value to decimal 0.10",
        scientific_meaning="requires a material disagreement between independently reconstructed discrete paths",
        provenance_class="V1_PREEXECUTION_NONTAUTOLOGICAL_PATH_POLICY",
    ),
    _provenance(
        "H_C",
        "minimum_consecutive_mismatch_steps",
        unit="consecutive postinitial steps",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_C/minimum_consecutive_violation_steps"],
        derivation_formula="2 adjacent steps",
        rounding_rule="exact integer",
        scientific_meaning="rejects a one-step mismatch spike",
        provenance_class="RENAMED_PREEXECUTION_V0_VALUE_FOR_V1_PATH_METRIC",
    ),
    _provenance(
        "H_C",
        "loose_to_tight_max_ratio_minimum",
        unit="dimensionless ratio",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_C/loose_to_tight_max_ratio_minimum"],
        derivation_formula="10/1",
        rounding_rule="exact binary64 integer ratio",
        scientific_meaning="requires the loose path mismatch to exceed tight R13 by one decade",
    ),
    _provenance(
        "H_C",
        "loose_to_neighbor_max_ratio_minimum",
        unit="dimensionless ratio",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_C/loose_to_neighbor_max_ratio_minimum"],
        derivation_formula="2/1",
        rounding_rule="exact binary64 integer ratio",
        scientific_meaning="requires R13-specific path mismatch beyond generic loose-tolerance behavior",
    ),
    _provenance(
        "H_C",
        "required_postinitial_step_count",
        unit="postinitial steps",
        source_record_ids=[
            f"{_V0_CONSTANT_ROOT}/H_C/required_postinitial_step_count",
            "/exact_run_matrix/common_numerics/accepted_step_count",
        ],
        derivation_formula="T/dt = 0.05/0.003125 = 16",
        rounding_rule="exact integer quotient required",
        scientific_meaning="requires complete independently reconstructed path histories",
        source_category="CANONICAL_HISTORY",
    ),
    _provenance(
        "H_C",
        "path_scale_floor_tolerance_multiplier",
        unit="multiple of requested solver tolerance",
        source_artifact=FREEZE_REVIEW_V0_RELATIVE_PATH,
        additional_source_artifacts=[DESIGN_REVIEW_V1_RELATIVE_PATH],
        source_record_ids=[_HC_REVIEW_FINDING, _DESIGN_OBLIGATION_ROOT],
        derivation_formula="1 * requested_solver_tolerance",
        rounding_rule="exact binary64 integer multiplier",
        scientific_meaning="prevents a near-zero path from manufacturing an unbounded relative mismatch",
        provenance_class="V1_PREEXECUTION_NONTAUTOLOGICAL_PATH_POLICY",
    ),
    _provenance(
        "H_D",
        "minimum_contributing_block_count_per_step",
        unit="packed solver blocks",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/minimum_contributing_block_count_per_step"],
        derivation_formula="smallest integer strictly greater than two",
        rounding_rule="exact integer",
        scientific_meaning="requires a genuinely distributed contribution across at least three blocks",
    ),
    _provenance(
        "H_D",
        "per_block_share_minimum",
        unit="normalized block-share fraction",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/per_block_share_minimum"],
        derivation_formula="1/10",
        rounding_rule="stored as the nearest binary64 value to decimal 0.10",
        scientific_meaning="defines a non-negligible per-block contribution",
    ),
    _provenance(
        "H_D",
        "effective_block_count_minimum",
        unit="inverse-participation effective block count",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/effective_block_count_minimum"],
        derivation_formula="minimum_contributing_block_count_per_step = 3",
        rounding_rule="exact binary64 integer value",
        scientific_meaning="requires effective participation by at least three equally weighted blocks",
    ),
    _provenance(
        "H_D",
        "single_block_share_maximum_exclusive",
        unit="normalized block-share fraction",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/single_block_share_maximum_exclusive"],
        derivation_formula="1/2, applied with a strict less-than comparator",
        rounding_rule="exact binary64 representation",
        scientific_meaning="excludes any step already dominated by one block",
    ),
    _provenance(
        "H_D",
        "distributed_step_fraction_minimum",
        unit="fraction of 16 postinitial steps",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/distributed_step_fraction_minimum"],
        derivation_formula="12/16",
        rounding_rule="exact binary64 representation of 3/4",
        scientific_meaning="requires distributed participation for at least twelve steps",
    ),
    _provenance(
        "H_D",
        "distributed_fraction_advantage_over_each_reference_minimum",
        unit="fractional-step advantage",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/distributed_fraction_advantage_over_each_reference_minimum"],
        derivation_formula="4/16",
        rounding_rule="exact binary64 representation of 1/4",
        scientific_meaning="requires at least four additional distributed steps versus each reference",
    ),
    _provenance(
        "H_D",
        "linked_structural_series_count",
        unit="registered structural series",
        source_record_ids=[
            f"{_V0_CONSTANT_ROOT}/H_D/linked_structural_series_count",
            f"{_V0_METRIC_ROOT}/linked_structural_series",
        ],
        derivation_formula="cardinality([GAUSS, CONTINUITY, LONGITUDINAL_EXCHANGE, LONGITUDINAL_MAXWELL])",
        rounding_rule="exact integer cardinality",
        scientific_meaning="requires every preregistered linked longitudinal diagnostic",
        source_category="CANONICAL_HISTORY",
    ),
    _provenance(
        "H_D",
        "minimum_nondecreasing_increments_per_series",
        unit="nondecreasing adjacent increments per 16-step series",
        source_record_ids=[f"{_V0_CONSTANT_ROOT}/H_D/minimum_nondecreasing_increments_per_series"],
        derivation_formula="(16-1)-1 = 14; at most one decreasing increment",
        rounding_rule="exact integer",
        scientific_meaning="requires persistent accumulation while admitting one finite-precision reversal",
    ),
)


LEGACY_Q: dict[str, Any] = {
    "contract_version": "v1",
    "status": "OPERATOR_CONSISTENCY_GATE_ONLY",
    "mechanism_decision_bearing": False,
    "may_support_H_C": False,
    "formula": "Q=(G1-G0)-(roll(Rp_derived,1)-Rp_derived)-a*dt*C_raw",
    "Rp_derived_formula": "Rp_derived=p1-p0+dt*grad_theta_midpoint_raw",
    "exact_arithmetic_value": 0,
    "operator_gate_rule": (
        "recompute every saved intermediate from raw inputs in the frozen NumPy "
        "operation order and require byte identity with the stored intermediate; "
        "Q magnitude and every gamma_n ratio are descriptive only"
    ),
    "failure_result": "BLOCKED_OPERATOR_BINDING",
    "gamma32_in_mechanism_decision_logic": False,
    "gamma_n_in_mechanism_decision_logic": False,
}


def _finite_array(value: Any, name: str) -> np.ndarray:
    array = np.asarray(value, dtype=np.float64)
    if array.ndim < 1 or array.size == 0:
        raise ValueError(f"{name} must be a nonempty array")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains a nonfinite value")
    return np.ascontiguousarray(array)


def reconstruct_independent_hc_paths(
    *,
    direct_terminal_p_equation_defect: Any,
    p_previous: Any,
    p_current: Any,
    rho_previous: Any,
    rho_current: Any,
    continuity_current_midpoint_independently_recomputed: Any,
    maxwell_source_midpoint_registered: Any,
    a: float,
    dt: float,
    requested_solver_tolerance: float,
) -> dict[str, Any]:
    """Reconstruct the two v1 decision-bearing H_C paths.

    Path A consumes the *stored terminal p-equation defect* emitted by the
    monolithic solver.  It is never re-derived from p/rho/current fields here.

    Path B consumes only raw p/rho fields and a current reconstructed through the
    independent Dirac-continuity route.  It must not consume the registered
    Maxwell-source array.  The latter is accepted separately and used only for
    the non-decision-bearing legacy-Q operator gate.  The two decision paths
    therefore share no derived residual or registered Maxwell source.

    Arrays may have shape ``(N,)`` for one step or ``(..., N)`` for a stack of
    steps.  The last axis is always the periodic lattice axis.
    """

    arrays = {
        "direct_terminal_p_equation_defect": _finite_array(
            direct_terminal_p_equation_defect,
            "direct_terminal_p_equation_defect",
        ),
        "p_previous": _finite_array(p_previous, "p_previous"),
        "p_current": _finite_array(p_current, "p_current"),
        "rho_previous": _finite_array(rho_previous, "rho_previous"),
        "rho_current": _finite_array(rho_current, "rho_current"),
        "continuity_current_midpoint_independently_recomputed": _finite_array(
            continuity_current_midpoint_independently_recomputed,
            "continuity_current_midpoint_independently_recomputed",
        ),
        "maxwell_source_midpoint_registered": _finite_array(
            maxwell_source_midpoint_registered,
            "maxwell_source_midpoint_registered",
        ),
    }
    shape = arrays["direct_terminal_p_equation_defect"].shape
    if any(array.shape != shape for array in arrays.values()):
        raise ValueError("all H_C path inputs must have exactly the same shape")
    spacing = float(a)
    step = float(dt)
    tolerance = float(requested_solver_tolerance)
    if not all(math.isfinite(value) for value in (spacing, step, tolerance)):
        raise ValueError("a, dt, and requested_solver_tolerance must be finite")
    if spacing <= 0.0 or step <= 0.0 or tolerance <= 0.0:
        raise ValueError("a, dt, and requested_solver_tolerance must be positive")

    direct_rp = arrays["direct_terminal_p_equation_defect"]
    p0 = arrays["p_previous"]
    p1 = arrays["p_current"]
    rho0 = arrays["rho_previous"]
    rho1 = arrays["rho_current"]
    continuity_current = arrays[
        "continuity_current_midpoint_independently_recomputed"
    ]
    maxwell_source = arrays["maxwell_source_midpoint_registered"]

    # Path A: direct solver-emitted terminal Maxwell defect only.
    maxwell_direct_path = np.roll(direct_rp, 1, axis=-1) - direct_rp

    # Path B: independently reconstructed Gauss drift minus raw continuity.
    gauss_previous_raw = np.roll(p0, 1, axis=-1) - p0 + spacing * rho0
    gauss_current_raw = np.roll(p1, 1, axis=-1) - p1 + spacing * rho1
    continuity_raw = (rho1 - rho0) / step + (
        continuity_current
        - np.roll(continuity_current, 1, axis=-1)
    ) / spacing
    continuity_gauss_raw_path = (
        gauss_current_raw
        - gauss_previous_raw
        - spacing * step * continuity_raw
    )
    mismatch = continuity_gauss_raw_path - maxwell_direct_path

    # Legacy Q is reconstructed separately and is never returned as the H_C
    # mechanism mismatch.  It remains a custody/operator-consistency witness.
    rp_derived_for_legacy_gate = p1 - p0 + step * maxwell_source
    continuity_registered_for_legacy_gate = (rho1 - rho0) / step + (
        maxwell_source - np.roll(maxwell_source, 1, axis=-1)
    ) / spacing
    legacy_q = (
        gauss_current_raw
        - gauss_previous_raw
        - (
            np.roll(rp_derived_for_legacy_gate, 1, axis=-1)
            - rp_derived_for_legacy_gate
        )
        - spacing * step * continuity_registered_for_legacy_gate
    )
    return {
        "maxwell_direct_terminal_defect_divergence": np.ascontiguousarray(
            maxwell_direct_path
        ),
        "continuity_gauss_raw_path": np.ascontiguousarray(
            continuity_gauss_raw_path
        ),
        "independent_path_mismatch": np.ascontiguousarray(mismatch),
        "gauss_previous_raw": np.ascontiguousarray(gauss_previous_raw),
        "gauss_current_raw": np.ascontiguousarray(gauss_current_raw),
        "continuity_raw": np.ascontiguousarray(continuity_raw),
        "continuity_current_midpoint_independently_recomputed": np.ascontiguousarray(
            continuity_current
        ),
        "maxwell_source_midpoint_registered_operator_gate_only": np.ascontiguousarray(
            maxwell_source
        ),
        "continuity_registered_operator_gate_only": np.ascontiguousarray(
            continuity_registered_for_legacy_gate
        ),
        "legacy_rp_derived_operator_gate_only": np.ascontiguousarray(
            rp_derived_for_legacy_gate
        ),
        "legacy_q_operator_gate_only": np.ascontiguousarray(legacy_q),
        "requested_solver_tolerance": tolerance,
        "lattice_axis": -1,
        "mechanism_path_sources_independent": True,
        "continuity_path_uses_registered_maxwell_source": False,
        "legacy_q_mechanism_decision_bearing": False,
    }


def _maximum_consecutive_true(mask: np.ndarray) -> int:
    maximum = 0
    current = 0
    for value in np.asarray(mask, dtype=bool).reshape(-1):
        if bool(value):
            current += 1
            maximum = max(maximum, current)
        else:
            current = 0
    return maximum


def summarize_independent_hc_paths(
    paths: Mapping[str, Any],
    *,
    relative_mismatch_minimum: float | None = None,
    path_scale_floor_tolerance_multiplier: float | None = None,
) -> dict[str, Any]:
    """Summarize independently reconstructed paths for the H_C classifier."""

    required = {
        "maxwell_direct_terminal_defect_divergence",
        "continuity_gauss_raw_path",
        "independent_path_mismatch",
        "requested_solver_tolerance",
        "mechanism_path_sources_independent",
        "legacy_q_mechanism_decision_bearing",
        "continuity_path_uses_registered_maxwell_source",
    }
    missing = sorted(required - set(paths))
    if missing:
        raise ValueError(f"H_C paths missing {missing[0]}")
    if paths["mechanism_path_sources_independent"] is not True:
        raise ValueError("H_C decision paths are not independently sourced")
    if paths["legacy_q_mechanism_decision_bearing"] is not False:
        raise ValueError("legacy Q must not enter H_C mechanism classification")
    if paths["continuity_path_uses_registered_maxwell_source"] is not False:
        raise ValueError("H_C continuity path reused the registered Maxwell source")

    maxwell = _finite_array(
        paths["maxwell_direct_terminal_defect_divergence"], "maxwell_direct_path"
    )
    continuity_gauss = _finite_array(
        paths["continuity_gauss_raw_path"], "continuity_gauss_raw_path"
    )
    mismatch = _finite_array(
        paths["independent_path_mismatch"], "independent_path_mismatch"
    )
    if maxwell.shape != continuity_gauss.shape or maxwell.shape != mismatch.shape:
        raise ValueError("H_C path and mismatch shapes must match")

    threshold = float(
        SUPPORT_CONSTANTS_V1["H_C"]["relative_path_mismatch_minimum"]
        if relative_mismatch_minimum is None
        else relative_mismatch_minimum
    )
    floor_multiplier = float(
        SUPPORT_CONSTANTS_V1["H_C"]["path_scale_floor_tolerance_multiplier"]
        if path_scale_floor_tolerance_multiplier is None
        else path_scale_floor_tolerance_multiplier
    )
    tolerance = float(paths["requested_solver_tolerance"])
    if not all(
        math.isfinite(value) for value in (threshold, floor_multiplier, tolerance)
    ):
        raise ValueError("H_C summary constants must be finite")
    if threshold < 0.0 or floor_multiplier <= 0.0 or tolerance <= 0.0:
        raise ValueError("H_C summary constants are outside their domains")

    # A one-dimensional input is one time sample.  Higher dimensions use their
    # first axis as time and reduce all remaining axes by L-infinity.
    if mismatch.ndim == 1:
        maxwell_linf = np.array([np.max(np.abs(maxwell))], dtype=np.float64)
        continuity_linf = np.array(
            [np.max(np.abs(continuity_gauss))], dtype=np.float64
        )
        mismatch_linf = np.array([np.max(np.abs(mismatch))], dtype=np.float64)
    else:
        reduction_axes = tuple(range(1, mismatch.ndim))
        maxwell_linf = np.max(np.abs(maxwell), axis=reduction_axes)
        continuity_linf = np.max(np.abs(continuity_gauss), axis=reduction_axes)
        mismatch_linf = np.max(np.abs(mismatch), axis=reduction_axes)
    floor = floor_multiplier * tolerance
    scale = np.maximum(np.maximum(maxwell_linf, continuity_linf), floor)
    relative = mismatch_linf / scale
    return {
        "max_relative_path_mismatch": float(np.max(relative)),
        "maximum_consecutive_mismatch_steps": _maximum_consecutive_true(
            relative >= threshold
        ),
        "relative_path_mismatch_by_step": [float(value) for value in relative],
        "maxwell_path_linf_by_step": [float(value) for value in maxwell_linf],
        "continuity_gauss_path_linf_by_step": [
            float(value) for value in continuity_linf
        ],
        "path_mismatch_linf_by_step": [float(value) for value in mismatch_linf],
        "path_scale_by_step": [float(value) for value in scale],
        "relative_mismatch_minimum": threshold,
        "path_scale_floor": floor,
        "path_scale_floor_tolerance_multiplier": floor_multiplier,
        "sample_count": int(relative.size),
        "gamma32_used": False,
        "legacy_q_used": False,
        "mechanism_path_sources_independent": True,
    }


# Exact 20 fields independently mutated by the v0 review.  The values are kept
# separately so consumers can use the stable field tuple without importing test
# fixture material into matrix-validation logic.
IDENTITY_MUTATION_FIELDS: tuple[str, ...] = (
    "parent_canonical_run_id",
    "parent_canonical_input_hash",
    "parent_canonical_output_sha256",
    "parent_canonical_output_path",
    "input_hash",
    "implementation_id",
    "implementation_sha256",
    "paired_run_id",
    "execution_role",
    "output_schema_version",
    "experiment_id",
    "scientific_row_id",
    "requested_axis_values",
    "parent_initial_condition_identity",
    "model_class",
    "numerical_method",
    "accepted_step_count",
    "checkpoint_count_including_initial",
    "instrumentation_read_only",
    "trajectory_identity_required",
)
IDENTITY_MUTATION_VALUES: dict[str, Any] = {
    "parent_canonical_run_id": "R00_CANONICAL:SOLVER_TOL1eM08",
    "parent_canonical_input_hash": "0" * 64,
    "parent_canonical_output_sha256": "0" * 64,
    "parent_canonical_output_path": "formal/output/WRONG.json",
    "input_hash": "0" * 64,
    "implementation_id": "WRONG_IMPLEMENTATION",
    "implementation_sha256": "0" * 64,
    "paired_run_id": "MECHv0:R13_TIGHT:INSTRUMENTED",
    "execution_role": "PAIRED_NONINSTRUMENTED_CONTROL",
    "output_schema_version": "v9",
    "experiment_id": "WRONG_EXPERIMENT",
    "scientific_row_id": "R00_CANONICAL",
    "requested_axis_values": {"WRONG": 1.0},
    "parent_initial_condition_identity": "WRONG_INITIAL_STATE",
    "model_class": "WRONG_MODEL",
    "numerical_method": "WRONG_METHOD",
    "accepted_step_count": 15,
    "checkpoint_count_including_initial": 16,
    "instrumentation_read_only": False,
    "trajectory_identity_required": False,
}


# Exact nine IDs reported missing by the independent v0 freeze review.
MISSING_REVIEW_CONTROL_IDS: tuple[str, ...] = (
    "M_FREEZE_DUPLICATE_PAYLOAD_IDENTITY",
    "M_FREEZE_OPERATOR_HELPER_HASH_CHANGED",
    "M_FREEZE_OUTPUT_ROOT_PREEXISTS",
    "M_FREEZE_RAW_EVIDENCE_FAILS_FAVORABLE_SUMMARY_TRUE",
    "M_FREEZE_REQUIRED_PAYLOAD_OMITTED",
    "M_FREEZE_UNKNOWN_MECHANISM_ID",
    "M_FREEZE_UNKNOWN_NINTH_SOLVER_BLOCK",
    "M_FREEZE_WORKTREE_GITATTRIBUTES_SUBSTITUTED",
    "M_FREEZE_WRONG_PARENT_CANONICAL_IDENTITY",
)


# Exact, hardcoded copies of the twelve controls registered in numerical-freeze
# packet v0.  These records are intentionally not loaded from that packet at
# runtime: the v1 contract must remain a pure, independently inspectable
# semantic witness rather than inheriting mutable or circular authority.
_V0_REGISTERED_CONTROLS: tuple[dict[str, Any], ...] = (
    {
        "control_id": "M_FREEZE_CANDIDATE_RUN_OMITTED",
        "mutation": "remove the final R10 noninstrumented record from the exact matrix",
        "expected_first_diagnostic": "RUN_MATRIX_COUNT_MISMATCH",
        "expected_evidence_result": "BLOCKED_RUN_IDENTITY",
        "expected_decision_change": "EVIDENCE_ADMISSIBILITY_TO_BLOCKED; hypotheses NOT_EVALUATED",
    },
    {
        "control_id": "M_FREEZE_R10_NEIGHBOR_DISPLACED",
        "mutation": "replace the R10 row payload in MECHv0:R10_LOOSE:INSTRUMENTED with any other row",
        "expected_first_diagnostic": "RUN_MATRIX_ROW_ID_MISMATCH:MECHv0:R10_LOOSE:INSTRUMENTED",
        "expected_evidence_result": "BLOCKED_RUN_IDENTITY",
        "expected_decision_change": "EXACT_NEIGHBOR_FREEZE_TO_BLOCKED",
    },
    {
        "control_id": "M_FREEZE_MULTIPLE_AGGREGATE_IDS_REMOVED",
        "mutation": "delete supported_mechanism_ids from a MULTIPLE_SUPPORTED_MECHANISMS result",
        "expected_first_diagnostic": "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
        "expected_evidence_result": "RESULT_INVALID",
        "expected_decision_change": "MULTIPLE_SUPPORTED_MECHANISMS_TO_REJECTED_RESULT",
    },
    {
        "control_id": "M_FREEZE_SUPPORTED_IDENTITY_SET_MISMATCH",
        "mutation": "replace ordered supported_mechanism_ids with a set inconsistent with individual decisions",
        "expected_first_diagnostic": "SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH",
        "expected_evidence_result": "RESULT_INVALID",
        "expected_decision_change": "SUPPORTED_RESULT_TO_REJECTED_RESULT",
    },
    {
        "control_id": "M_FREEZE_H_D_WITHOUT_POSITIVE_EVIDENCE",
        "mutation": "mark H_D SUPPORTED while one or more H_D necessary criteria are FAILED",
        "expected_first_diagnostic": "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR_AWARDED_WITHOUT_POSITIVE_EVIDENCE",
        "expected_evidence_result": "RESULT_INVALID",
        "expected_decision_change": "H_D_SUPPORTED_TO_REJECTED_RESULT",
    },
    {
        "control_id": "M_FREEZE_H_E_WITH_MISSING_OBSERVABLE",
        "mutation": "after required_observables_complete=false blocks evidence, illegally mark H_E SUPPORTED and label the aggregate unresolved",
        "expected_first_diagnostic": "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
        "expected_evidence_result": "RESULT_INVALID",
        "expected_decision_change": "ILLEGAL_H_E_UNRESOLVED_TO_REJECTED_RESULT",
    },
    {
        "control_id": "M_FREEZE_CLASSIFICATION_AFTER_NONPERTURBATION_FAILURE",
        "mutation": "after instrumentation_nonperturbation_passed=false blocks evidence, illegally mark one physical hypothesis SUPPORTED",
        "expected_first_diagnostic": "CLASSIFICATION_PERFORMED_AFTER_EVIDENCE_BLOCK",
        "expected_evidence_result": "RESULT_INVALID",
        "expected_decision_change": "POST_BLOCK_CLASSIFICATION_TO_REJECTED_RESULT",
    },
    {
        "control_id": "M_FREEZE_CONTINUUM_OPERATOR_SUBSTITUTED",
        "mutation": "set discrete_operator_binding_passed false after substituting a continuum operator",
        "expected_first_diagnostic": "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
        "expected_evidence_result": "BLOCKED_OPERATOR_BINDING",
        "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
    },
    {
        "control_id": "M_FREEZE_OUTPUT_ROOT_COLLIDES_CANONICAL",
        "mutation": "set the future experiment output root equal to or inside the canonical output root",
        "expected_first_diagnostic": "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
        "expected_evidence_result": "BLOCKED_CUSTODY",
        "expected_decision_change": "SEPARATE_OUTPUT_CUSTODY_TO_BLOCKED",
    },
    {
        "control_id": "M_FREEZE_TRAJECTORY_BYTE_MISMATCH",
        "mutation": "change one packed float64 state byte in one instrumented trajectory only",
        "expected_first_diagnostic": "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL",
        "expected_evidence_result": "BLOCKED_INSTRUMENTATION_PERTURBATION",
        "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; no fallback equivalence",
    },
    {
        "control_id": "M_FREEZE_OBSERVABLE_UNITS_OR_NORMALIZATION_MISSING",
        "mutation": "remove one required unit, normalization scale, floor, or aggregation binding",
        "expected_first_diagnostic": "OBSERVABLE_UNIT_OR_NORMALIZATION_INVALID",
        "expected_evidence_result": "BLOCKED_OBSERVABLE_SEMANTICS",
        "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
    },
    {
        "control_id": "M_FREEZE_UNKNOWN_OR_DUPLICATE_RUN_ID",
        "mutation": "replace one expected run ID with an unknown ID or duplicate an earlier expected run ID",
        "expected_first_diagnostic_by_variant": {
            "DUPLICATE_RUN_ID": "DUPLICATE_RUN_IDENTITY",
            "UNKNOWN_RUN_ID": "EXPECTED_RUN_ID_CLOSURE_MISMATCH",
        },
        "expected_evidence_result": "BLOCKED_RUN_IDENTITY",
        "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
    },
)


_MISSING_CONTROL_CONTRACTS: dict[str, tuple[str, str, str]] = {
    "M_FREEZE_DUPLICATE_PAYLOAD_IDENTITY": (
        "duplicate a run/payload-role identity or relative path",
        "DUPLICATE_PAYLOAD_IDENTITY",
        "BLOCKED_RUN_IDENTITY",
    ),
    "M_FREEZE_OPERATOR_HELPER_HASH_CHANGED": (
        "change one loaded evolution/pack/operator-helper byte or loaded module path",
        "LOADED_OPERATOR_MODULE_IDENTITY_MISMATCH",
        "BLOCKED_OPERATOR_BINDING",
    ),
    "M_FREEZE_OUTPUT_ROOT_PREEXISTS": (
        "create the mechanism output root before the one-shot preflight",
        "MECHANISM_OUTPUT_ROOT_PREEXISTS",
        "BLOCKED_CUSTODY",
    ),
    "M_FREEZE_RAW_EVIDENCE_FAILS_FAVORABLE_SUMMARY_TRUE": (
        "corrupt one raw observable while retaining a favorable stored summary",
        "RAW_SUMMARY_RECOMPUTATION_MISMATCH",
        "BLOCKED_OBSERVABLE_SEMANTICS",
    ),
    "M_FREEZE_REQUIRED_PAYLOAD_OMITTED": (
        "remove one of the twelve registered JSON/NPZ payload identities",
        "REQUIRED_OUTPUT_MISSING",
        "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
    ),
    "M_FREEZE_UNKNOWN_MECHANISM_ID": (
        "insert a mechanism ID outside ordered [H_A,H_B,H_C,H_D]",
        "UNKNOWN_MECHANISM_ID",
        "RESULT_REJECTED",
    ),
    "M_FREEZE_UNKNOWN_NINTH_SOLVER_BLOCK": (
        "insert a ninth block outside the exact packed 22N registry",
        "SOLVER_BLOCK_REGISTRY_MISMATCH",
        "BLOCKED_OBSERVABLE_SEMANTICS",
    ),
    "M_FREEZE_WORKTREE_GITATTRIBUTES_SUBSTITUTED": (
        "substitute working-tree .gitattributes bytes for the committed Git blob",
        "COMMITTED_CONFIGURATION_BYTES_MISMATCH",
        "BLOCKED_CUSTODY",
    ),
    "M_FREEZE_WRONG_PARENT_CANONICAL_IDENTITY": (
        "replace a run's registered canonical parent identity",
        "PARENT_CANONICAL_IDENTITY_MISMATCH",
        "BLOCKED_RUN_IDENTITY",
    ),
}


def _build_full_adversarial_registry() -> tuple[dict[str, Any], ...]:
    records: list[dict[str, Any]] = []
    for registered_control in _V0_REGISTERED_CONTROLS:
        records.append(
            {
                **registered_control,
                "category": "PRESERVED_V0_REGISTERED_CONTROL",
                "source_artifact": FREEZE_V0_RELATIVE_PATH,
            }
        )
    for control_id in MISSING_REVIEW_CONTROL_IDS:
        mutation, diagnostic, decision = _MISSING_CONTROL_CONTRACTS[control_id]
        records.append(
            {
                "control_id": control_id,
                "category": "V0_REVIEW_REQUIRED_MISSING_CONTROL",
                "mutation": mutation,
                "expected_first_diagnostic": diagnostic,
                "expected_decision_change": decision,
                "source_artifact": FREEZE_REVIEW_V0_RELATIVE_PATH,
            }
        )
    for field in IDENTITY_MUTATION_FIELDS:
        records.append(
            {
                "control_id": f"M_FREEZE_MATRIX_IDENTITY_FIELD_{field.upper()}",
                "category": "V0_REVIEW_EXACT_MATRIX_IDENTITY_MUTATION",
                "mutation": {
                    "field": field,
                    "replacement": IDENTITY_MUTATION_VALUES[field],
                },
                "expected_first_diagnostic": (
                    f"RUN_MATRIX_IDENTITY_FIELD_MISMATCH:{field}"
                ),
                "expected_decision_change": "BLOCKED_RUN_IDENTITY",
                "source_artifact": FREEZE_REVIEW_V0_RELATIVE_PATH,
            }
        )
    ids = [record["control_id"] for record in records]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate control ID in full v1 adversarial registry")
    return tuple(records)


FULL_ADVERSARIAL_REGISTRY_V1: tuple[dict[str, Any], ...] = (
    _build_full_adversarial_registry()
)


def validate_semantic_contract() -> list[str]:
    """Return deterministic contract-structure diagnostics without any simulation."""

    errors: list[str] = []
    leaves = [
        (hypothesis, constant_id)
        for hypothesis, constants in SUPPORT_CONSTANTS_V1.items()
        for constant_id in constants
    ]
    if len(leaves) != 23:
        errors.append("SUPPORT_CONSTANT_LEAF_COUNT_MISMATCH")
    provenance_keys = [
        (record["hypothesis"], record["constant_id"])
        for record in SUPPORT_CONSTANT_PROVENANCE
    ]
    if len(SUPPORT_CONSTANT_PROVENANCE) != 23:
        errors.append("SUPPORT_CONSTANT_PROVENANCE_COUNT_MISMATCH")
    if len(provenance_keys) != len(set(provenance_keys)):
        errors.append("SUPPORT_CONSTANT_PROVENANCE_DUPLICATE")
    if set(provenance_keys) != set(leaves):
        errors.append("SUPPORT_CONSTANT_PROVENANCE_CLOSURE_MISMATCH")
    required_provenance_fields = {
        "hypothesis",
        "constant_id",
        "value",
        "unit",
        "units",
        "role",
        "source_category",
        "source_commit",
        "source_artifact",
        "source_record_ids",
        "derivation_formula",
        "rounding_rule",
        "scientific_meaning",
        "decision_bearing_or_descriptive",
        "nonfuture",
        "future_mechanism_outputs_used",
    }
    if any(
        not required_provenance_fields <= set(record)
        or record["source_category"] not in SOURCE_CATEGORIES
        or record["source_commit"] != UNCOMMITTED_SOURCE_SENTINEL
        or record["decision_bearing_or_descriptive"] != "DECISION_BEARING"
        or record["nonfuture"] is not True
        or record["future_mechanism_outputs_used"] is not False
        or not record["source_record_ids"]
        for record in SUPPORT_CONSTANT_PROVENANCE
    ):
        errors.append("SUPPORT_CONSTANT_PROVENANCE_FIELD_INCOMPLETE")
    if len(IDENTITY_MUTATION_FIELDS) != 20 or len(set(IDENTITY_MUTATION_FIELDS)) != 20:
        errors.append("IDENTITY_MUTATION_FIELD_CLOSURE_MISMATCH")
    if set(IDENTITY_MUTATION_VALUES) != set(IDENTITY_MUTATION_FIELDS):
        errors.append("IDENTITY_MUTATION_VALUE_CLOSURE_MISMATCH")
    if len(MISSING_REVIEW_CONTROL_IDS) != 9 or len(set(MISSING_REVIEW_CONTROL_IDS)) != 9:
        errors.append("MISSING_REVIEW_CONTROL_ID_CLOSURE_MISMATCH")
    full_ids = [record["control_id"] for record in FULL_ADVERSARIAL_REGISTRY_V1]
    if len(full_ids) != len(set(full_ids)):
        errors.append("FULL_ADVERSARIAL_REGISTRY_DUPLICATE_ID")
    if not set(MISSING_REVIEW_CONTROL_IDS) <= set(full_ids):
        errors.append("FULL_ADVERSARIAL_REGISTRY_MISSING_REVIEW_CONTROL")
    identity_control_ids = {
        f"M_FREEZE_MATRIX_IDENTITY_FIELD_{field.upper()}"
        for field in IDENTITY_MUTATION_FIELDS
    }
    if not identity_control_ids <= set(full_ids):
        errors.append("FULL_ADVERSARIAL_REGISTRY_MISSING_IDENTITY_MUTATION")
    preserved_v0_controls = [
        record
        for record in FULL_ADVERSARIAL_REGISTRY_V1
        if record["category"] == "PRESERVED_V0_REGISTERED_CONTROL"
    ]
    generic_placeholder_fragments = (
        "preserve the exact v0 registered mutation semantics",
        "preserve registered mutation semantics",
        "placeholder",
        "to be specified",
        "tbd",
    )
    if len(preserved_v0_controls) != 12:
        errors.append("PRESERVED_V0_ADVERSARIAL_CONTROL_COUNT_MISMATCH")
    if any(
        not isinstance(record.get("mutation"), str)
        or not record["mutation"].strip()
        or any(
            fragment in record["mutation"].casefold()
            for fragment in generic_placeholder_fragments
        )
        for record in preserved_v0_controls
    ):
        errors.append("PRESERVED_V0_ADVERSARIAL_MUTATION_PLACEHOLDER")
    if any(
        "expected_decision_change" not in record
        or "expected_evidence_result" not in record
        or not (
            "expected_first_diagnostic" in record
            or "expected_first_diagnostic_by_variant" in record
        )
        for record in preserved_v0_controls
    ):
        errors.append("PRESERVED_V0_ADVERSARIAL_EXPECTATION_INCOMPLETE")
    if LEGACY_Q["mechanism_decision_bearing"] is not False:
        errors.append("LEGACY_Q_STILL_DECISION_BEARING")
    if any("gamma" in key.casefold() for key in SUPPORT_CONSTANTS_V1["H_C"]):
        errors.append("H_C_GAMMA_CONSTANT_REMAINS")
    return errors


__all__ = [
    "CONTRACT_ID",
    "FULL_ADVERSARIAL_REGISTRY_V1",
    "IDENTITY_MUTATION_FIELDS",
    "IDENTITY_MUTATION_VALUES",
    "LEGACY_Q",
    "MISSING_REVIEW_CONTROL_IDS",
    "SCRIPT_RELATIVE_PATH",
    "SOURCE_CATEGORIES",
    "SUPPORT_CONSTANTS_V1",
    "SUPPORT_CONSTANT_PROVENANCE",
    "UNCOMMITTED_SOURCE_SENTINEL",
    "reconstruct_independent_hc_paths",
    "summarize_independent_hc_paths",
    "validate_semantic_contract",
]
