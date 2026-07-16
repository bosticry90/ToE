from __future__ import annotations

"""Non-executing instrumentation support for the R13 mechanism experiment.

This module has no command-line entry point, performs no work on import, and does
not create or modify output files.  It provides pure array helpers plus an
explicitly callable observer-enabled reproduction of the historical Picard loop.
The historical RHS and state constructor remain authoritative; the callable
runner exposes their packed residuals and preregisterable mechanism observables
without changing the physical equations or numerical update order.
"""

import hashlib
import importlib
import io
import json
import math
import os
import platform
import struct
import zipfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

import numpy as np


IMPLEMENTATION_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_IMPLEMENTATION_v0"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_implementation_v0.py"
)
OUTPUT_SCHEMA_VERSION = "v0"
EXPECTED_PYTHON_VERSION = "3.10.11"
EXPECTED_NUMPY_VERSION = "2.2.6"
REQUIRED_EXECUTION_ENVIRONMENT = {
    "PYTHONHASHSEED": "0",
    "TZ": "UTC",
    "LC_ALL": "C",
    "LANG": "C",
    "OPENBLAS_NUM_THREADS": "1",
    "OMP_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
}
RUN_PAYLOAD_JSON_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RUN_PAYLOAD_JSON_v0"
)
RUN_PAYLOAD_NPZ_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RUN_PAYLOAD_NPZ_v0"
)
MATRIX_RESULT_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_MATRIX_RESULT_v0"
)
EXACT_MATRIX_RUN_IDS = [
    "MECHv0:R13_LOOSE:INSTRUMENTED",
    "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL",
    "MECHv0:R13_TIGHT:INSTRUMENTED",
    "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL",
    "MECHv0:R10_LOOSE:INSTRUMENTED",
    "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL",
]
EXPECTED_OUTPUT_PATHS_BY_RUN_ID = {
    "MECHv0:R13_LOOSE:INSTRUMENTED": {
        "json_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "00-MECHv0_R13_LOOSE_INSTRUMENTED.json"
        ),
        "npz_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "00-MECHv0_R13_LOOSE_INSTRUMENTED.npz"
        ),
    },
    "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL": {
        "json_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "01-MECHv0_R13_LOOSE_NONINSTRUMENTED_CONTROL.json"
        ),
        "npz_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "01-MECHv0_R13_LOOSE_NONINSTRUMENTED_CONTROL.npz"
        ),
    },
    "MECHv0:R13_TIGHT:INSTRUMENTED": {
        "json_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "02-MECHv0_R13_TIGHT_INSTRUMENTED.json"
        ),
        "npz_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "02-MECHv0_R13_TIGHT_INSTRUMENTED.npz"
        ),
    },
    "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL": {
        "json_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "03-MECHv0_R13_TIGHT_NONINSTRUMENTED_CONTROL.json"
        ),
        "npz_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "03-MECHv0_R13_TIGHT_NONINSTRUMENTED_CONTROL.npz"
        ),
    },
    "MECHv0:R10_LOOSE:INSTRUMENTED": {
        "json_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "04-MECHv0_R10_LOOSE_INSTRUMENTED.json"
        ),
        "npz_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "04-MECHv0_R10_LOOSE_INSTRUMENTED.npz"
        ),
    },
    "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL": {
        "json_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "05-MECHv0_R10_LOOSE_NONINSTRUMENTED_CONTROL.json"
        ),
        "npz_relative_output_path": (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0/"
            "05-MECHv0_R10_LOOSE_NONINSTRUMENTED_CONTROL.npz"
        ),
    },
}
CLASSIFIER_ROLE_BY_INSTRUMENTED_RUN_ID = {
    "MECHv0:R13_LOOSE:INSTRUMENTED": "R13_LOOSE",
    "MECHv0:R13_TIGHT:INSTRUMENTED": "R13_TIGHT",
    "MECHv0:R10_LOOSE:INSTRUMENTED": "R10_LOOSE_NEIGHBOR",
}
EXPECTED_ROW_ID_BY_RUN_ID = {
    "MECHv0:R13_LOOSE:INSTRUMENTED": "R13_CORNER_STRONG_LOW",
    "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL": "R13_CORNER_STRONG_LOW",
    "MECHv0:R13_TIGHT:INSTRUMENTED": "R13_CORNER_STRONG_LOW",
    "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL": "R13_CORNER_STRONG_LOW",
    "MECHv0:R10_LOOSE:INSTRUMENTED": "R10_MU_HIGH",
    "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL": "R10_MU_HIGH",
}
EXPECTED_ROW_PARAMETERS = {
    "R13_CORNER_STRONG_LOW": {
        "row_id": "R13_CORNER_STRONG_LOW",
        "ETA_Q": 0.4,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.0634205964176414,
        "THETA_W": 0.3,
        "DELTA_THETA_PSI": -1.5707963267948966,
        "MU_MASS_DOMAIN": 2.0,
    },
    "R10_MU_HIGH": {
        "row_id": "R10_MU_HIGH",
        "ETA_Q": 0.2,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.2131315883288088,
        "THETA_W": 0.3,
        "DELTA_THETA_PSI": 0.0,
        "MU_MASS_DOMAIN": 2.0,
    },
}
EXPECTED_TOLERANCE_BY_RUN_ID = {
    "MECHv0:R13_LOOSE:INSTRUMENTED": 1.0e-8,
    "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL": 1.0e-8,
    "MECHv0:R13_TIGHT:INSTRUMENTED": 1.0e-12,
    "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL": 1.0e-12,
    "MECHv0:R10_LOOSE:INSTRUMENTED": 1.0e-8,
    "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL": 1.0e-8,
}
EXPECTED_EXPERIMENT_NUMERICS = {
    "n": 16,
    "dt": 0.003125,
    "duration": 0.05,
    "max_iterations": 80,
}
EXPECTED_EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)
EXPECTED_CANONICAL_ROOT_RELATIVE_PATH = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)
EXPECTED_CANONICAL_ROOT_DIGEST_DOMAIN = "AUTHORITY_CHAIN_CANONICAL_JSON_INVENTORY"
EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256 = (
    "886541953dfcfecfffa44b2ff9e2ee62c14c468139042bf4f3477ef3a1f2a721"
)
EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256_DOMAIN = (
    "R13-MECHANISM-DIRECTORY-TREE-v0"
)

# These registries are deliberately literal top-level values so a freeze-packet
# generator can inspect them with ``ast.literal_eval`` without importing this
# module or loading any numerical implementation.
BLOCK_REGISTRY = [
    {
        "block_id": "THETA_KINEMATIC",
        "packed_span_in_units_of_n": [0, 1],
        "metric": "MAX_ABSOLUTE_PACKED_REAL",
    },
    {
        "block_id": "P_LONGITUDINAL_MAXWELL",
        "packed_span_in_units_of_n": [1, 2],
        "metric": "MAX_ABSOLUTE_PACKED_REAL",
    },
    {
        "block_id": "PHI2_KINEMATIC",
        "packed_span_in_units_of_n": [2, 3],
        "metric": "MAX_ABSOLUTE_PACKED_REAL",
    },
    {
        "block_id": "P2_DYNAMIC",
        "packed_span_in_units_of_n": [3, 4],
        "metric": "MAX_ABSOLUTE_PACKED_REAL",
    },
    {
        "block_id": "PHI3_KINEMATIC",
        "packed_span_in_units_of_n": [4, 5],
        "metric": "MAX_ABSOLUTE_PACKED_REAL",
    },
    {
        "block_id": "P3_DYNAMIC",
        "packed_span_in_units_of_n": [5, 6],
        "metric": "MAX_ABSOLUTE_PACKED_REAL",
    },
    {
        "block_id": "DIRAC_PLUS",
        "packed_span_in_units_of_n": [6, 14],
        "metric": "MAX_ABSOLUTE_PACKED_REAL_RE_AND_IM_AGGREGATED",
    },
    {
        "block_id": "DIRAC_MINUS",
        "packed_span_in_units_of_n": [14, 22],
        "metric": "MAX_ABSOLUTE_PACKED_REAL_RE_AND_IM_AGGREGATED",
    },
]
OBSERVABLE_IDS = [
    "EXCHANGE_FIELD_LONGITUDINAL_RAW",
    "EXCHANGE_MATTER_LONGITUDINAL_RAW",
    "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
    "EXCHANGE_CANCELLATION_KAPPA",
    "SOLVER_BLOCK_RESIDUAL_RAW",
    "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
    "SOLVER_BLOCK_DOMINANCE_FRACTION",
    "SOLVER_ITERATION_METADATA",
    "GAUSS_RESIDUAL_FIELD",
    "CONTINUITY_RESIDUAL_FIELD",
    "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
    "DISCRETE_OPERATOR_OUTPUTS",
    "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
    "INSTRUMENTATION_TRAJECTORY_IDENTITY",
]
DISCRETE_CLOSURE_CONTRACT = {
    "periodic_backward_shift": "roll(field,1)",
    "gauss": "G=roll(p,1)-p+a*rho",
    "p_equation_defect": "Rp=p1-p0+dt*grad_theta_mid",
    "continuity": (
        "C=(rho1-rho0)/dt+"
        "(grad_theta_mid-roll(grad_theta_mid,1))/a"
    ),
    "closure_q": "Q=(G1-G0)-(roll(Rp,1)-Rp)-a*dt*C",
    "roundoff_bound": (
        "B=gamma32*(|roll(p1,1)|+|p1|+|a*rho1|+|roll(p0,1)|+"
        "|p0|+|a*rho0|+|roll(Rp,1)|+|Rp|+|a*dt*C|)"
    ),
    "roundoff_ratio": "abs(Q)/B; 0/0=0; positive/0 is invalid",
    "gamma_operation_count": 32,
    "binary64_unit_roundoff": "2^-53",
    "continuum_substitution_allowed": False,
}

# Read-only bindings to the implementation whose trajectories and residuals are
# being observed.  The optional source-binding helper below never writes them.
BOUND_SOURCE_SHA256 = {
    (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_non_authoritative_pilot_v1.py"
    ): "05e7015499e3d15bc172840ac637fd0fa86b6c50f87489d6b555657ac290adb6",
    (
        "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_"
        "pilot.py"
    ): "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}

PACKED_COMPONENTS_PER_SITE = 22
PACKED_RESIDUAL_BLOCK_IDS = (
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
    "PHI2_KINEMATIC",
    "P2_DYNAMIC",
    "PHI3_KINEMATIC",
    "P3_DYNAMIC",
    "DIRAC_PLUS",
    "DIRAC_MINUS",
)
LONGITUDINAL_BLOCK_IDS = (
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
)

# IEEE-754 binary64 unit roundoff and Higham's gamma_n model.  The operation
# counts are part of the proposed diagnostic semantics, not fitted quantities.
FLOAT64_UNIT_ROUNDOFF = 2.0**-53


def gamma_n(operation_count: int) -> float:
    """Return gamma_n = n*u/(1-n*u) for binary64 arithmetic."""

    if isinstance(operation_count, bool) or not isinstance(operation_count, int):
        raise TypeError("operation_count must be an integer")
    if operation_count <= 0:
        raise ValueError("operation_count must be positive")
    product = operation_count * FLOAT64_UNIT_ROUNDOFF
    if product >= 1.0:
        raise ValueError("operation_count is outside the gamma_n model domain")
    return product / (1.0 - product)


GAMMA32 = gamma_n(32)
GAMMA64 = gamma_n(64)

# Exact formulas exposed for custody packets and freeze documents.
DISCRETE_CLOSURE_Q_FORMULA = (
    "Q=(G1-G0)-(roll(Rp,1)-Rp)-a*dt*C; "
    "G=roll(p,1)-p+a*rho; Rp=p1-p0+dt*grad_theta_mid; "
    "C=(rho1-rho0)/dt+(grad_theta_mid-roll(grad_theta_mid,1))/a"
)
DISCRETE_CLOSURE_BOUND_FORMULA = (
    "B=gamma32*(|roll(p1,1)|+|p1|+|a*rho1|+|roll(p0,1)|+|p0|+"
    "|a*rho0|+|roll(Rp,1)|+|Rp|+|a*dt*C|)"
)
EXCHANGE_CONDITIONING_FORMULA = (
    "kappa=(|X_field|+|X_matter|)/"
    "(|X_field+X_matter|+gamma64*(|X_field|+|X_matter|))"
)

RUN_ROLE_PAYLOAD_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RUN_ROLE_PAYLOAD_v0"
)
HISTORICAL_EVOLUTION_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_non_authoritative_pilot_v1"
)
HISTORICAL_PACK_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_non_authoritative_pilot"
)
MANDATORY_INSTRUMENTED_EVENT_FAMILIES = (
    "exchange",
    "terminal_equation_blocks",
    "solver_steps",
    "spatial_constraints",
    "discrete_closure",
)


def _finite_float64_array(
    value: Any,
    name: str,
    *,
    ndim: int | None = None,
) -> np.ndarray:
    array = np.asarray(value, dtype=np.float64)
    if ndim is not None and array.ndim != ndim:
        raise ValueError(f"{name} must have ndim={ndim}, got {array.ndim}")
    if array.size == 0:
        raise ValueError(f"{name} must be nonempty")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} contains a nonfinite value")
    return np.ascontiguousarray(array)


def _positive_integer(value: int, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, (int, np.integer)):
        raise TypeError(f"{name} must be an integer")
    result = int(value)
    if result <= 0:
        raise ValueError(f"{name} must be positive")
    return result


def packed_residual_block_slices(n: int) -> dict[str, slice]:
    """Return the eight exact block slices used by the historical ``pack``.

    ``DIRAC_PLUS`` and ``DIRAC_MINUS`` each aggregate their packed real and
    imaginary arrays.  Norms over those slices are therefore packed-real norms,
    not reconstructed complex magnitudes.
    """

    n = _positive_integer(n, "n")
    return {
        "THETA_KINEMATIC": slice(0, n),
        "P_LONGITUDINAL_MAXWELL": slice(n, 2 * n),
        "PHI2_KINEMATIC": slice(2 * n, 3 * n),
        "P2_DYNAMIC": slice(3 * n, 4 * n),
        "PHI3_KINEMATIC": slice(4 * n, 5 * n),
        "P3_DYNAMIC": slice(5 * n, 6 * n),
        "DIRAC_PLUS": slice(6 * n, 14 * n),
        "DIRAC_MINUS": slice(14 * n, 22 * n),
    }


def infer_lattice_size(packed_vector: Any) -> int:
    """Infer ``n`` from a one-dimensional historical packed vector."""

    vector = _finite_float64_array(packed_vector, "packed_vector", ndim=1)
    if vector.size % PACKED_COMPONENTS_PER_SITE != 0:
        raise ValueError(
            "packed_vector length must be an exact multiple of "
            f"{PACKED_COMPONENTS_PER_SITE}"
        )
    return vector.size // PACKED_COMPONENTS_PER_SITE


def split_packed_residual(
    packed_residual: Any,
    n: int | None = None,
    *,
    copy: bool = True,
) -> dict[str, np.ndarray]:
    """Split a supplied packed equation or Picard residual into eight blocks."""

    residual = _finite_float64_array(packed_residual, "packed_residual", ndim=1)
    lattice_size = infer_lattice_size(residual) if n is None else _positive_integer(n, "n")
    expected = PACKED_COMPONENTS_PER_SITE * lattice_size
    if residual.size != expected:
        raise ValueError(
            f"packed_residual has length {residual.size}; expected {expected} for n={lattice_size}"
        )
    result = {
        block_id: residual[block_slice]
        for block_id, block_slice in packed_residual_block_slices(lattice_size).items()
    }
    return {key: value.copy() for key, value in result.items()} if copy else result


def packed_residual_block_maxima(
    packed_residual: Any,
    n: int | None = None,
) -> dict[str, float]:
    """Return max-absolute packed-real magnitude for every residual block."""

    blocks = split_packed_residual(packed_residual, n, copy=False)
    return {
        block_id: float(np.max(np.abs(block)))
        for block_id, block in blocks.items()
    }


def implicit_midpoint_equation_defect(
    previous_packed_state: Any,
    current_packed_state: Any,
    midpoint_rhs_packed: Any,
    dt: float,
) -> np.ndarray:
    """Compute the historical implicit-midpoint equation defect.

    The caller supplies the RHS already evaluated by the historical evolution
    implementation.  This helper never invokes the RHS or advances a state.
    """

    previous = _finite_float64_array(previous_packed_state, "previous_packed_state", ndim=1)
    current = _finite_float64_array(current_packed_state, "current_packed_state", ndim=1)
    midpoint_rhs = _finite_float64_array(midpoint_rhs_packed, "midpoint_rhs_packed", ndim=1)
    if previous.shape != current.shape or previous.shape != midpoint_rhs.shape:
        raise ValueError("packed state and midpoint RHS shapes must match exactly")
    step = float(dt)
    if not math.isfinite(step) or step <= 0.0:
        raise ValueError("dt must be finite and positive")
    return np.ascontiguousarray(current - previous - step * midpoint_rhs)


def normalize_block_residuals(
    raw_block_magnitudes: Mapping[str, Any],
    block_scales: Mapping[str, Any],
    block_floors: Mapping[str, Any],
) -> dict[str, float]:
    """Normalize eight raw block magnitudes by ``max(scale, floor)``.

    Scales and floors are explicit caller inputs so this support module does not
    smuggle unfrozen numerical constants into the experiment.
    """

    expected = set(PACKED_RESIDUAL_BLOCK_IDS)
    for name, mapping in (
        ("raw_block_magnitudes", raw_block_magnitudes),
        ("block_scales", block_scales),
        ("block_floors", block_floors),
    ):
        if set(mapping) != expected:
            raise ValueError(f"{name} must contain exactly the eight registered block IDs")
    result: dict[str, float] = {}
    for block_id in PACKED_RESIDUAL_BLOCK_IDS:
        raw = float(raw_block_magnitudes[block_id])
        scale = float(block_scales[block_id])
        floor = float(block_floors[block_id])
        if not all(math.isfinite(value) for value in (raw, scale, floor)):
            raise ValueError(f"nonfinite normalization input for {block_id}")
        if raw < 0.0 or scale < 0.0 or floor <= 0.0:
            raise ValueError(
                f"{block_id} requires raw>=0, scale>=0, and floor>0"
            )
        result[block_id] = raw / max(scale, floor)
    return result


def block_dominance_shares(
    normalized_by_block: Mapping[str, Any],
    epsilon_dominance: float,
) -> dict[str, np.ndarray]:
    """Compute per-sample block shares from normalized residual magnitudes."""

    if set(normalized_by_block) != set(PACKED_RESIDUAL_BLOCK_IDS):
        raise ValueError("normalized_by_block must contain exactly eight registered blocks")
    epsilon = float(epsilon_dominance)
    if not math.isfinite(epsilon) or epsilon < 0.0:
        raise ValueError("epsilon_dominance must be finite and nonnegative")
    arrays = {
        block_id: _finite_float64_array(
            normalized_by_block[block_id], f"normalized_by_block[{block_id}]", ndim=1
        )
        for block_id in PACKED_RESIDUAL_BLOCK_IDS
    }
    shape = arrays[PACKED_RESIDUAL_BLOCK_IDS[0]].shape
    if any(array.shape != shape for array in arrays.values()):
        raise ValueError("all normalized block series must have the same shape")
    if any(np.any(array < 0.0) for array in arrays.values()):
        raise ValueError("normalized block magnitudes must be nonnegative")
    total = np.sum(np.stack(list(arrays.values()), axis=0), axis=0) + epsilon
    if np.any(total <= 0.0):
        raise ValueError("zero block total requires a positive epsilon_dominance")
    return {block_id: arrays[block_id] / total for block_id in PACKED_RESIDUAL_BLOCK_IDS}


def summarize_block_dominance(
    share_by_block: Mapping[str, Any],
) -> dict[str, Any]:
    """Build the exact H_B-facing block-dominance summary fields."""

    if set(share_by_block) != set(PACKED_RESIDUAL_BLOCK_IDS):
        raise ValueError("share_by_block must contain exactly eight registered blocks")
    arrays = {
        block_id: _finite_float64_array(
            share_by_block[block_id], f"share_by_block[{block_id}]", ndim=1
        )
        for block_id in PACKED_RESIDUAL_BLOCK_IDS
    }
    shape = arrays[PACKED_RESIDUAL_BLOCK_IDS[0]].shape
    if any(array.shape != shape for array in arrays.values()):
        raise ValueError("all block-share series must have the same shape")
    if any(np.any((array < 0.0) | (array > 1.0)) for array in arrays.values()):
        raise ValueError("block shares must lie in [0, 1]")
    matrix = np.stack([arrays[block_id] for block_id in PACKED_RESIDUAL_BLOCK_IDS], axis=1)
    medians = np.median(matrix, axis=0)
    dominant_index = int(np.argmax(medians))
    dominant_block_id = PACKED_RESIDUAL_BLOCK_IDS[dominant_index]
    step_winners = np.argmax(matrix, axis=1)
    return {
        "dominant_block_id": dominant_block_id,
        "median_dominance_share": float(medians[dominant_index]),
        "dominant_step_fraction": float(np.mean(step_winners == dominant_index)),
        "median_share_by_block": {
            block_id: float(medians[index])
            for index, block_id in enumerate(PACKED_RESIDUAL_BLOCK_IDS)
        },
        "sample_count": int(matrix.shape[0]),
    }


def exchange_conditioning_series(
    x_field: Any,
    x_matter: Any,
) -> dict[str, np.ndarray | float | int]:
    """Compute raw exchange terms and additive-gamma64 conditioning.

    The gamma64 floor is ``gamma(64) * (|X_field| + |X_matter|)``.  If both
    terms are zero, the numerator and kappa are defined as zero.
    """

    field = _finite_float64_array(x_field, "x_field")
    matter = _finite_float64_array(x_matter, "x_matter")
    if field.shape != matter.shape:
        raise ValueError("x_field and x_matter shapes must match")
    numerator = np.abs(field) + np.abs(matter)
    remainder = field + matter
    floor = GAMMA64 * numerator
    denominator = np.abs(remainder) + floor
    kappa = np.zeros_like(numerator)
    np.divide(numerator, denominator, out=kappa, where=numerator > 0.0)
    return {
        "x_field": field,
        "x_matter": matter,
        "remainder": remainder,
        "conditioning_numerator": numerator,
        "gamma64_floor": floor,
        "kappa": kappa,
        "gamma_operation_count": 64,
        "gamma64": GAMMA64,
    }


def summarize_exchange_conditioning(
    x_field: Any,
    x_matter: Any,
    severe_kappa_threshold: float,
) -> dict[str, Any]:
    """Build the exact H_A-facing exchange-conditioning summary fields."""

    threshold = float(severe_kappa_threshold)
    if not math.isfinite(threshold) or threshold <= 0.0:
        raise ValueError("severe_kappa_threshold must be finite and positive")
    series = exchange_conditioning_series(x_field, x_matter)
    kappa = np.asarray(series["kappa"], dtype=np.float64).reshape(-1)
    return {
        "median_kappa": float(np.median(kappa)),
        "severe_step_fraction": float(np.mean(kappa >= threshold)),
        "sample_count": int(kappa.size),
        "severe_kappa_threshold": threshold,
        "gamma_operation_count": 64,
        "gamma64": GAMMA64,
    }


def _roundoff_ratio(numerator: np.ndarray, bound: np.ndarray) -> np.ndarray:
    ratio = np.zeros_like(numerator, dtype=np.float64)
    positive_bound = bound > 0.0
    np.divide(numerator, bound, out=ratio, where=positive_bound)
    impossible = (~positive_bound) & (numerator > 0.0)
    ratio[impossible] = math.inf
    return ratio


def discrete_maxwell_continuity_closure(
    p_previous: Any,
    p_current: Any,
    rho_previous: Any,
    rho_current: Any,
    grad_theta_midpoint: Any,
    a: float,
    dt: float,
) -> dict[str, np.ndarray | float | int]:
    """Evaluate the exact implemented Maxwell-to-continuity closure Q/bound.

    ``grad_theta_midpoint`` is the actual midpoint matter observable used by the
    historical RHS.  Periodicity is the historical ``np.roll(..., 1)`` rule.
    The p-equation defect is retained, so Q tests the implemented identity rather
    than silently assuming an exact p solve.
    """

    arrays = {
        "p_previous": _finite_float64_array(p_previous, "p_previous", ndim=1),
        "p_current": _finite_float64_array(p_current, "p_current", ndim=1),
        "rho_previous": _finite_float64_array(rho_previous, "rho_previous", ndim=1),
        "rho_current": _finite_float64_array(rho_current, "rho_current", ndim=1),
        "grad_theta_midpoint": _finite_float64_array(
            grad_theta_midpoint, "grad_theta_midpoint", ndim=1
        ),
    }
    shape = arrays["p_previous"].shape
    if any(array.shape != shape for array in arrays.values()):
        raise ValueError("all closure fields must have the same one-dimensional shape")
    spacing = float(a)
    step = float(dt)
    if not math.isfinite(spacing) or spacing <= 0.0:
        raise ValueError("a must be finite and positive")
    if not math.isfinite(step) or step <= 0.0:
        raise ValueError("dt must be finite and positive")

    p0 = arrays["p_previous"]
    p1 = arrays["p_current"]
    rho0 = arrays["rho_previous"]
    rho1 = arrays["rho_current"]
    grad = arrays["grad_theta_midpoint"]
    gauss0 = np.roll(p0, 1) - p0 + spacing * rho0
    gauss1 = np.roll(p1, 1) - p1 + spacing * rho1
    p_equation_defect = p1 - p0 + step * grad
    continuity = (rho1 - rho0) / step + (grad - np.roll(grad, 1)) / spacing
    defect_divergence = np.roll(p_equation_defect, 1) - p_equation_defect
    continuity_increment = spacing * step * continuity
    q = (gauss1 - gauss0) - defect_divergence - continuity_increment

    # Conservative absolute-term scale for the complete scheme-derived identity.
    roundoff_scale = (
        np.abs(np.roll(p1, 1))
        + np.abs(p1)
        + np.abs(spacing * rho1)
        + np.abs(np.roll(p0, 1))
        + np.abs(p0)
        + np.abs(spacing * rho0)
        + np.abs(np.roll(p_equation_defect, 1))
        + np.abs(p_equation_defect)
        + np.abs(continuity_increment)
    )
    bound = GAMMA32 * roundoff_scale
    ratio = _roundoff_ratio(np.abs(q), bound)
    return {
        "p_previous": p0.copy(),
        "p_current": p1.copy(),
        "rho_previous": rho0.copy(),
        "rho_current": rho1.copy(),
        "grad_theta_midpoint": grad.copy(),
        "gauss_previous": gauss0,
        "gauss_current": gauss1,
        "p_equation_defect": p_equation_defect,
        "continuity_residual": continuity,
        "p_defect_divergence": defect_divergence,
        "continuity_increment": continuity_increment,
        "closure_q": q,
        "roundoff_scale": roundoff_scale,
        "roundoff_bound": bound,
        "roundoff_bound_ratio": ratio,
        "gamma_operation_count": 32,
        "gamma32": GAMMA32,
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


def summarize_discrete_closure(
    closure_q: Any,
    roundoff_bound: Any,
) -> dict[str, Any]:
    """Build the exact H_C-facing Q/gamma32-bound summary fields."""

    q = _finite_float64_array(closure_q, "closure_q")
    bound = _finite_float64_array(roundoff_bound, "roundoff_bound")
    if q.shape != bound.shape:
        raise ValueError("closure_q and roundoff_bound shapes must match")
    if np.any(bound < 0.0):
        raise ValueError("roundoff_bound must be nonnegative")
    # Each leading element is treated as one post-initial time sample; any
    # remaining dimensions are spatial and reduced by max, matching H_C.
    if q.ndim == 1:
        q_by_step = np.abs(q)
        bound_by_step = bound
    else:
        axes = tuple(range(1, q.ndim))
        ratio_full = _roundoff_ratio(np.abs(q), bound)
        ratio_by_step = np.max(ratio_full, axis=axes)
        if np.any(~np.isfinite(ratio_by_step)):
            raise ValueError("positive Q with zero roundoff bound")
        return {
            "max_roundoff_bound_ratio": float(np.max(ratio_by_step)),
            "maximum_consecutive_violation_steps": _maximum_consecutive_true(
                ratio_by_step > 1.0
            ),
            "sample_count": int(q.shape[0]),
            "gamma_operation_count": 32,
            "gamma32": GAMMA32,
        }
    ratio_by_step = _roundoff_ratio(q_by_step, bound_by_step)
    if np.any(~np.isfinite(ratio_by_step)):
        raise ValueError("positive Q with zero roundoff bound")
    return {
        "max_roundoff_bound_ratio": float(np.max(ratio_by_step)),
        "maximum_consecutive_violation_steps": _maximum_consecutive_true(
            ratio_by_step > 1.0
        ),
        "sample_count": int(q_by_step.size),
        "gamma_operation_count": 32,
        "gamma32": GAMMA32,
    }


def summarize_distributed_accumulation(
    share_by_block: Mapping[str, Any],
    linked_structural_series: Mapping[str, Any],
    *,
    per_block_share_minimum: float,
    minimum_contributing_block_count: int,
    effective_block_count_minimum: float,
    single_block_share_maximum_exclusive: float,
) -> dict[str, Any]:
    """Build the exact H_D-facing distributed-accumulation summary fields."""

    if set(share_by_block) != set(PACKED_RESIDUAL_BLOCK_IDS):
        raise ValueError("share_by_block must contain exactly eight registered blocks")
    arrays = {
        block_id: _finite_float64_array(
            share_by_block[block_id], f"share_by_block[{block_id}]", ndim=1
        )
        for block_id in PACKED_RESIDUAL_BLOCK_IDS
    }
    shape = arrays[PACKED_RESIDUAL_BLOCK_IDS[0]].shape
    if any(array.shape != shape for array in arrays.values()):
        raise ValueError("all block-share series must have the same shape")
    matrix = np.stack([arrays[block_id] for block_id in PACKED_RESIDUAL_BLOCK_IDS], axis=1)
    if np.any((matrix < 0.0) | (matrix > 1.0)):
        raise ValueError("block shares must lie in [0, 1]")

    share_minimum = float(per_block_share_minimum)
    count_minimum = _positive_integer(
        minimum_contributing_block_count, "minimum_contributing_block_count"
    )
    effective_minimum = float(effective_block_count_minimum)
    single_maximum = float(single_block_share_maximum_exclusive)
    if not all(
        math.isfinite(value)
        for value in (share_minimum, effective_minimum, single_maximum)
    ):
        raise ValueError("distributed thresholds must be finite")
    if not 0.0 <= share_minimum <= 1.0:
        raise ValueError("per_block_share_minimum must lie in [0, 1]")
    if effective_minimum <= 0.0:
        raise ValueError("effective_block_count_minimum must be positive")
    if not 0.0 < single_maximum <= 1.0:
        raise ValueError("single_block_share_maximum_exclusive must lie in (0, 1]")

    contributing_count = np.sum(matrix >= share_minimum, axis=1)
    share_total = np.sum(matrix, axis=1)
    square_total = np.sum(matrix**2, axis=1)
    effective_count = np.zeros(matrix.shape[0], dtype=np.float64)
    np.divide(
        share_total**2,
        square_total,
        out=effective_count,
        where=square_total > 0.0,
    )
    maximum_share = np.max(matrix, axis=1)
    qualifying = (
        (contributing_count >= count_minimum)
        & (effective_count >= effective_minimum)
        & (maximum_share < single_maximum)
    )

    if not isinstance(linked_structural_series, Mapping) or not linked_structural_series:
        raise ValueError("linked_structural_series must be a nonempty mapping")
    linked = {
        str(series_id): _finite_float64_array(
            values, f"linked_structural_series[{series_id}]", ndim=1
        )
        for series_id, values in linked_structural_series.items()
    }
    linked_shape = next(iter(linked.values())).shape
    if any(array.shape != linked_shape for array in linked.values()):
        raise ValueError("all linked structural series must have the same shape")
    maxima_at_final = sum(
        bool(array[-1] == np.max(array)) for array in linked.values()
    )
    nondecreasing_counts = [
        int(np.sum(np.diff(array) >= 0.0)) for array in linked.values()
    ]
    return {
        "distributed_step_fraction": float(np.mean(qualifying)),
        "linked_series_maxima_at_final_count": int(maxima_at_final),
        "minimum_nondecreasing_increment_count": int(min(nondecreasing_counts)),
        "sample_count": int(matrix.shape[0]),
        "linked_series_count": int(len(linked)),
        "contributing_block_count_by_step": [int(value) for value in contributing_count],
        "effective_block_count_by_step": [float(value) for value in effective_count],
        "maximum_block_share_by_step": [float(value) for value in maximum_share],
    }


_PHYSICAL_TRAJECTORY_DOMAIN = b"R13-MECHANISM-PHYSICAL-TRAJECTORY-v0\x00"


def physical_trajectory_projection(
    snapshots: Sequence[Any],
    *,
    packed_state_field: str = "packed_state",
) -> np.ndarray:
    """Project snapshots to the physical packed-state trajectory only.

    A snapshot may be a packed vector directly or a mapping containing
    ``packed_state_field``.  All instrumentation-only fields are ignored.
    """

    if isinstance(snapshots, (str, bytes, bytearray)) or not isinstance(
        snapshots, Sequence
    ):
        raise TypeError("snapshots must be a sequence")
    if len(snapshots) == 0:
        raise ValueError("snapshots must be nonempty")
    vectors: list[np.ndarray] = []
    for index, snapshot in enumerate(snapshots):
        value = snapshot
        if isinstance(snapshot, Mapping):
            if packed_state_field not in snapshot:
                raise ValueError(
                    f"snapshot {index} lacks physical field {packed_state_field!r}"
                )
            value = snapshot[packed_state_field]
        vector = _finite_float64_array(value, f"snapshot[{index}]", ndim=1)
        infer_lattice_size(vector)
        vectors.append(vector)
    width = vectors[0].size
    if any(vector.size != width for vector in vectors):
        raise ValueError("all physical snapshots must have the same packed length")
    return np.ascontiguousarray(np.stack(vectors, axis=0), dtype=np.float64)


def physical_trajectory_sha256(
    snapshots: Sequence[Any],
    *,
    packed_state_field: str = "packed_state",
) -> str:
    """Hash the little-endian float64 physical projection with shape framing."""

    projection = physical_trajectory_projection(
        snapshots, packed_state_field=packed_state_field
    )
    little_endian = np.ascontiguousarray(projection.astype("<f8", copy=False))
    digest = hashlib.sha256()
    digest.update(_PHYSICAL_TRAJECTORY_DOMAIN)
    digest.update(struct.pack("<QQ", little_endian.shape[0], little_endian.shape[1]))
    digest.update(little_endian.tobytes(order="C"))
    return digest.hexdigest()


def compare_physical_trajectories(
    instrumented_snapshots: Sequence[Any],
    control_snapshots: Sequence[Any],
    *,
    packed_state_field: str = "packed_state",
) -> dict[str, Any]:
    """Return byte-identity evidence for an instrumented/control trajectory pair."""

    instrumented = physical_trajectory_projection(
        instrumented_snapshots, packed_state_field=packed_state_field
    )
    control = physical_trajectory_projection(
        control_snapshots, packed_state_field=packed_state_field
    )
    instrumented_hash = physical_trajectory_sha256(
        instrumented_snapshots, packed_state_field=packed_state_field
    )
    control_hash = physical_trajectory_sha256(
        control_snapshots, packed_state_field=packed_state_field
    )
    shape_equal = instrumented.shape == control.shape
    byte_equal = bool(
        shape_equal
        and instrumented.dtype == control.dtype
        and instrumented.tobytes(order="C") == control.tobytes(order="C")
    )
    return {
        "byte_identical": byte_equal,
        "shape_identical": shape_equal,
        "instrumented_sha256": instrumented_hash,
        "control_sha256": control_hash,
        "instrumented_shape": list(instrumented.shape),
        "control_shape": list(control.shape),
    }


def _load_historical_implementation() -> tuple[Any, Any]:
    """Lazily import the bound evolution and pack modules.

    Importing this instrumentation module alone therefore does not even load the
    historical experiment implementation.  The imports occur only when a caller
    explicitly invokes a step or role runner.
    """

    evolution = importlib.import_module(HISTORICAL_EVOLUTION_MODULE)
    packed = importlib.import_module(HISTORICAL_PACK_MODULE)
    return evolution, packed


def _validate_metric_configuration(metric_configuration: Mapping[str, Any]) -> None:
    required = {
        "block_scales",
        "block_floors",
        "epsilon_dominance",
        "severe_kappa_threshold",
        "distributed_per_block_share_minimum",
        "distributed_minimum_contributing_block_count",
        "distributed_effective_block_count_minimum",
        "distributed_single_block_share_maximum_exclusive",
    }
    if not isinstance(metric_configuration, Mapping):
        raise TypeError("metric_configuration must be a mapping")
    missing = sorted(required - set(metric_configuration))
    if missing:
        raise ValueError(f"metric_configuration missing {missing[0]}")
    # Reuse the public normalizer for exact block-ID and scalar validation.
    normalize_block_residuals(
        {block_id: 0.0 for block_id in PACKED_RESIDUAL_BLOCK_IDS},
        metric_configuration["block_scales"],
        metric_configuration["block_floors"],
    )
    epsilon = float(metric_configuration["epsilon_dominance"])
    severe = float(metric_configuration["severe_kappa_threshold"])
    if not math.isfinite(epsilon) or epsilon <= 0.0:
        raise ValueError("epsilon_dominance must be finite and positive")
    if not math.isfinite(severe) or severe <= 0.0:
        raise ValueError("severe_kappa_threshold must be finite and positive")


def picard_midpoint_step_with_observer(
    packed_state: Any,
    n: int,
    q: float,
    mass: float,
    dt: float,
    tolerance: float,
    max_iterations: int,
    *,
    observer_enabled: bool,
) -> dict[str, Any]:
    """Execute one historical Picard-midpoint step with optional read-only tracing.

    The arithmetic update order is the historical order: explicit predictor,
    Picard midpoint update, max-absolute update residual, assignment, tolerance
    test, and one terminal equation-defect evaluation.  There is no Newton step,
    Jacobian, preconditioner, line search, damping, rejection, or retry.
    """

    evolution, _ = _load_historical_implementation()
    vector = _finite_float64_array(packed_state, "packed_state", ndim=1)
    lattice_size = _positive_integer(n, "n")
    if vector.size != PACKED_COMPONENTS_PER_SITE * lattice_size:
        raise ValueError("packed_state length does not match n")
    charge = float(q)
    runtime_mass = float(mass)
    step = float(dt)
    requested_tolerance = float(tolerance)
    iteration_cap = _positive_integer(max_iterations, "max_iterations")
    if not all(
        math.isfinite(value)
        for value in (charge, runtime_mass, step, requested_tolerance)
    ):
        raise ValueError("q, mass, dt, and tolerance must be finite")
    if step <= 0.0 or requested_tolerance <= 0.0:
        raise ValueError("dt and tolerance must be positive")
    if type(observer_enabled) is not bool:
        raise TypeError("observer_enabled must be bool")

    def evaluate(value: np.ndarray) -> np.ndarray:
        return evolution.rhs(
            value,
            lattice_size,
            charge,
            runtime_mass,
            False,
        )

    guess = vector + step * evaluate(vector)
    converged = False
    update_residual = math.inf
    iteration_events: list[dict[str, Any]] = []
    for iteration in range(1, iteration_cap + 1):
        updated = vector + step * evaluate(0.5 * (vector + guess))
        update_defect = updated - guess
        update_residual = float(np.max(np.abs(update_defect)))
        if observer_enabled:
            iteration_events.append(
                {
                    # The initial explicit predictor is fixed-point state 0;
                    # the first computed update therefore records R^(0).
                    "iteration": iteration - 1,
                    "update_ordinal": iteration,
                    "packed_update_defect": update_defect.copy(),
                    "packed_real_block_maxima": packed_residual_block_maxima(
                        update_defect, lattice_size
                    ),
                    "maximum_absolute_update_defect": update_residual,
                }
            )
        guess = updated
        if update_residual <= requested_tolerance:
            converged = True
            break

    midpoint_rhs = evaluate(0.5 * (vector + guess))
    equation_defect = guess - vector - step * midpoint_rhs
    equation_residual = float(np.max(np.abs(equation_defect)))
    solver_residual = max(update_residual, equation_residual)
    return {
        "packed_state": guess,
        "solver_residual": solver_residual,
        "update_residual": update_residual,
        "equation_residual": equation_residual,
        "iterations": iteration,
        "converged": converged,
        "stopping_reason": (
            "TOLERANCE_REACHED" if converged else "MAX_ITERATIONS_REACHED"
        ),
        "step_accepted": True,
        "requested_tolerance": requested_tolerance,
        "packed_terminal_equation_defect": equation_defect,
        "packed_terminal_midpoint_rhs": midpoint_rhs,
        "iteration_events": iteration_events if observer_enabled else None,
        "algorithm": "MONOLITHIC_PICARD_FIXED_POINT_IMPLICIT_MIDPOINT",
        "damping": "NOT_APPLICABLE",
        "line_search": "NOT_APPLICABLE",
        "jacobian": "NOT_AVAILABLE_PICARD_METHOD",
        "preconditioner": "NOT_AVAILABLE_PICARD_METHOD",
        "conditioning_estimate": "NOT_AVAILABLE_FROM_HISTORICAL_SOLVER",
    }


def _terminal_block_event(
    packed_defect: np.ndarray,
    n: int,
    metric_configuration: Mapping[str, Any],
) -> dict[str, Any]:
    raw = packed_residual_block_maxima(packed_defect, n)
    normalized = normalize_block_residuals(
        raw,
        metric_configuration["block_scales"],
        metric_configuration["block_floors"],
    )
    shares = block_dominance_shares(
        {block_id: np.array([normalized[block_id]]) for block_id in PACKED_RESIDUAL_BLOCK_IDS},
        float(metric_configuration["epsilon_dominance"]),
    )
    return {
        "packed_terminal_equation_defect": packed_defect.copy(),
        "packed_real_block_maxima": raw,
        "normalized_block_magnitudes": normalized,
        "dominance_share_by_block": {
            block_id: float(shares[block_id][0])
            for block_id in PACKED_RESIDUAL_BLOCK_IDS
        },
    }


def _metric_summaries_from_events(
    raw_events: Mapping[str, Any],
    metric_configuration: Mapping[str, Any],
) -> dict[str, Any]:
    exchange_events = raw_events["exchange"]
    terminal_events = raw_events["terminal_equation_blocks"]
    closure_events = raw_events["discrete_closure"]
    constraint_events = raw_events["spatial_constraints"]
    share_series = {
        block_id: np.array(
            [event["dominance_share_by_block"][block_id] for event in terminal_events],
            dtype=np.float64,
        )
        for block_id in PACKED_RESIDUAL_BLOCK_IDS
    }
    exchange_summary = summarize_exchange_conditioning(
        np.array([event["x_field_integral"] for event in exchange_events]),
        np.array([event["x_matter_integral"] for event in exchange_events]),
        float(metric_configuration["severe_kappa_threshold"]),
    )
    block_summary = summarize_block_dominance(share_series)
    q = np.stack([event["closure_q"] for event in closure_events], axis=0)
    bound = np.stack([event["roundoff_bound"] for event in closure_events], axis=0)
    closure_summary = summarize_discrete_closure(q, bound)
    linked = {
        "GAUSS": np.array(
            [event["gauss_maximum_absolute"] for event in constraint_events]
        ),
        "CONTINUITY": np.array(
            [event["continuity_maximum_absolute"] for event in constraint_events]
        ),
        "LONGITUDINAL_EXCHANGE": np.array(
            [abs(event["remainder_integral"]) for event in exchange_events]
        ),
        "LONGITUDINAL_MAXWELL": np.array(
            [
                max(
                    event["packed_real_block_maxima"]["THETA_KINEMATIC"],
                    event["packed_real_block_maxima"]["P_LONGITUDINAL_MAXWELL"],
                )
                for event in terminal_events
            ]
        ),
    }
    distributed_summary = summarize_distributed_accumulation(
        share_series,
        linked,
        per_block_share_minimum=float(
            metric_configuration["distributed_per_block_share_minimum"]
        ),
        minimum_contributing_block_count=int(
            metric_configuration["distributed_minimum_contributing_block_count"]
        ),
        effective_block_count_minimum=float(
            metric_configuration["distributed_effective_block_count_minimum"]
        ),
        single_block_share_maximum_exclusive=float(
            metric_configuration[
                "distributed_single_block_share_maximum_exclusive"
            ]
        ),
    )
    return {
        "exchange_conditioning": exchange_summary,
        "block_dominance": block_summary,
        "discrete_closure": closure_summary,
        "distributed_accumulation": distributed_summary,
    }


def run_role_in_memory(
    row: Mapping[str, Any],
    role_id: str,
    n: int,
    dt: float,
    duration: float,
    tolerance: float,
    max_iterations: int,
    *,
    instrumentation_enabled: bool,
    metric_configuration: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Run one full-model role and return a validated in-memory payload.

    This callable is deliberately not connected to a CLI or ``__main__`` block.
    A future accepted execution driver may call it, but importing this module or
    preparing a freeze cannot start a run.
    """

    if type(instrumentation_enabled) is not bool:
        raise TypeError("instrumentation_enabled must be bool")
    if instrumentation_enabled:
        if metric_configuration is None:
            raise ValueError("instrumented roles require metric_configuration")
        _validate_metric_configuration(metric_configuration)
    elif metric_configuration is not None:
        # Controls may carry the same frozen config for identity, but it is not
        # evaluated and therefore cannot alter their physical path.
        _validate_metric_configuration(metric_configuration)

    evolution, packed = _load_historical_implementation()
    lattice_size = _positive_integer(n, "n")
    requested_dt = float(dt)
    final_time = float(duration)
    requested_tolerance = float(tolerance)
    if not all(
        math.isfinite(value)
        for value in (requested_dt, final_time, requested_tolerance)
    ):
        raise ValueError("dt, duration, and tolerance must be finite")
    if requested_dt <= 0.0 or final_time <= 0.0 or requested_tolerance <= 0.0:
        raise ValueError("dt, duration, and tolerance must be positive")
    steps = max(1, int(round(final_time / requested_dt)))
    effective_dt = final_time / steps
    row_copy = dict(row)
    required_row_fields = {
        "row_id",
        "ETA_Q",
        "F_PERP_POSITIVE_LOADING_INITIAL_v1",
        "THETA_W",
        "DELTA_THETA_PSI",
        "MU_MASS_DOMAIN",
    }
    missing_row = sorted(required_row_fields - set(row_copy))
    if missing_row:
        raise ValueError(f"row missing {missing_row[0]}")
    mass = float(row_copy["MU_MASS_DOMAIN"]) / evolution.LENGTH
    charge = float(row_copy["ETA_Q"]) * mass
    spacing = evolution.LENGTH / lattice_size
    state, reconstruction = evolution.construct_initial_state(
        row_copy, lattice_size, False
    )
    vector = packed.pack(state)
    physical_snapshots = [vector.copy()]
    times = [0.0]
    raw_events: dict[str, list[dict[str, Any]]] | None = (
        {family: [] for family in MANDATORY_INSTRUMENTED_EVENT_FAMILIES}
        if instrumentation_enabled
        else None
    )
    all_steps_converged = True
    maximum_iterations_used = 0
    maximum_solver_residual = 0.0

    for step_index in range(1, steps + 1):
        previous_vector = vector
        step_result = picard_midpoint_step_with_observer(
            previous_vector,
            lattice_size,
            charge,
            mass,
            effective_dt,
            requested_tolerance,
            max_iterations,
            observer_enabled=instrumentation_enabled,
        )
        vector = np.asarray(step_result["packed_state"], dtype=np.float64)
        physical_snapshots.append(vector.copy())
        times.append(step_index * effective_dt)
        all_steps_converged = all_steps_converged and bool(step_result["converged"])
        maximum_iterations_used = max(
            maximum_iterations_used, int(step_result["iterations"])
        )
        maximum_solver_residual = max(
            maximum_solver_residual, float(step_result["solver_residual"])
        )
        if not instrumentation_enabled:
            continue

        assert raw_events is not None
        assert metric_configuration is not None
        previous_state = packed.unpack(previous_vector, lattice_size)
        current_state = packed.unpack(vector, lattice_size)
        midpoint_state = packed.unpack(0.5 * (previous_vector + vector), lattice_size)
        previous_obs = evolution.matter_observables(
            previous_state, spacing, charge, mass
        )
        current_obs = evolution.matter_observables(current_state, spacing, charge, mass)
        midpoint_obs = evolution.matter_observables(
            midpoint_state, spacing, charge, mass
        )
        previous_energy = evolution.energy_components(
            previous_state, spacing, charge, mass
        )
        current_energy = evolution.energy_components(
            current_state, spacing, charge, mass
        )

        field_cell_contribution = (
            current_state["p"] ** 2 - previous_state["p"] ** 2
        ) / (2.0 * spacing)
        theta_dot = midpoint_state["p"] / spacing
        matter_cell_contribution = (
            effective_dt * midpoint_obs["grad_theta"] * theta_dot
        )
        x_field = (
            current_energy["electric_fluctuating"]
            + current_energy["electric_zero_mode"]
            - previous_energy["electric_fluctuating"]
            - previous_energy["electric_zero_mode"]
        )
        x_matter = float(np.sum(matter_cell_contribution))
        conditioning = exchange_conditioning_series(
            np.array([x_field]), np.array([x_matter])
        )
        raw_events["exchange"].append(
            {
                "step": step_index,
                "time": step_index * effective_dt,
                "x_field_cell_contribution": field_cell_contribution.copy(),
                "x_matter_cell_contribution": matter_cell_contribution.copy(),
                "x_field_integral": float(x_field),
                "x_matter_integral": float(x_matter),
                "remainder_integral": float(np.asarray(conditioning["remainder"])[0]),
                "conditioning_numerator": float(
                    np.asarray(conditioning["conditioning_numerator"])[0]
                ),
                "gamma64_floor": float(np.asarray(conditioning["gamma64_floor"])[0]),
                "kappa": float(np.asarray(conditioning["kappa"])[0]),
            }
        )

        terminal_event = _terminal_block_event(
            np.asarray(step_result["packed_terminal_equation_defect"]),
            lattice_size,
            metric_configuration,
        )
        terminal_event.update({"step": step_index, "time": step_index * effective_dt})
        raw_events["terminal_equation_blocks"].append(terminal_event)
        enriched_iteration_events: list[dict[str, Any]] = []
        for iteration_event in step_result["iteration_events"]:
            event_copy = dict(iteration_event)
            normalized_iteration_blocks = normalize_block_residuals(
                event_copy["packed_real_block_maxima"],
                metric_configuration["block_scales"],
                metric_configuration["block_floors"],
            )
            iteration_shares = block_dominance_shares(
                {
                    block_id: np.array(
                        [normalized_iteration_blocks[block_id]], dtype=np.float64
                    )
                    for block_id in PACKED_RESIDUAL_BLOCK_IDS
                },
                float(metric_configuration["epsilon_dominance"]),
            )
            event_copy["normalized_block_magnitudes"] = (
                normalized_iteration_blocks
            )
            event_copy["dominance_share_by_block"] = {
                block_id: float(iteration_shares[block_id][0])
                for block_id in PACKED_RESIDUAL_BLOCK_IDS
            }
            enriched_iteration_events.append(event_copy)
        raw_events["solver_steps"].append(
            {
                "step": step_index,
                "time": step_index * effective_dt,
                "requested_tolerance": requested_tolerance,
                "terminal_solver_residual": float(step_result["solver_residual"]),
                "terminal_update_residual": float(step_result["update_residual"]),
                "terminal_equation_residual": float(step_result["equation_residual"]),
                "stopping_reason": step_result["stopping_reason"],
                "step_accepted": bool(step_result["step_accepted"]),
                "converged": bool(step_result["converged"]),
                "iteration_count": int(step_result["iterations"]),
                "terminal_iteration_state_index": int(step_result["iterations"]),
                "iteration_events": enriched_iteration_events,
                "algorithm": step_result["algorithm"],
                "damping": step_result["damping"],
                "line_search": step_result["line_search"],
                "jacobian": step_result["jacobian"],
                "preconditioner": step_result["preconditioner"],
                "conditioning_estimate": step_result["conditioning_estimate"],
            }
        )

        gauss = (
            np.roll(current_state["p"], 1)
            - current_state["p"]
            + spacing * current_obs["rho"]
        )
        continuity = (
            (current_obs["rho"] - previous_obs["rho"]) / effective_dt
            + (
                midpoint_obs["grad_theta"]
                - np.roll(midpoint_obs["grad_theta"], 1)
            )
            / spacing
        )
        terminal_blocks = split_packed_residual(
            step_result["packed_terminal_equation_defect"], lattice_size, copy=False
        )
        theta_defect = terminal_blocks["THETA_KINEMATIC"]
        p_defect = terminal_blocks["P_LONGITUDINAL_MAXWELL"]
        raw_events["spatial_constraints"].append(
            {
                "step": step_index,
                "time": step_index * effective_dt,
                "gauss_residual_field": gauss.copy(),
                "continuity_residual_field": continuity.copy(),
                "longitudinal_theta_equation_defect": theta_defect.copy(),
                "longitudinal_p_equation_defect": p_defect.copy(),
                "gauss_maximum_absolute": float(np.max(np.abs(gauss))),
                "continuity_maximum_absolute": float(np.max(np.abs(continuity))),
                "gauss_grid_weighted_l2": float(
                    math.sqrt(spacing * float(np.sum(gauss**2)))
                ),
                "continuity_grid_weighted_l2": float(
                    math.sqrt(spacing * float(np.sum(continuity**2)))
                ),
                "gauss_lowest_index_argmax": int(np.argmax(np.abs(gauss))),
                "continuity_lowest_index_argmax": int(
                    np.argmax(np.abs(continuity))
                ),
                "longitudinal_theta_grid_weighted_l2": float(
                    math.sqrt(spacing * float(np.sum(theta_defect**2)))
                ),
                "longitudinal_p_grid_weighted_l2": float(
                    math.sqrt(spacing * float(np.sum(p_defect**2)))
                ),
                "longitudinal_theta_lowest_index_argmax": int(
                    np.argmax(np.abs(theta_defect))
                ),
                "longitudinal_p_lowest_index_argmax": int(
                    np.argmax(np.abs(p_defect))
                ),
            }
        )
        closure = discrete_maxwell_continuity_closure(
            previous_state["p"],
            current_state["p"],
            previous_obs["rho"],
            current_obs["rho"],
            midpoint_obs["grad_theta"],
            spacing,
            effective_dt,
        )
        forward_matrix = (
            -1j * evolution.ALPHA1 - evolution.WILSON_R * evolution.BETA
        ) / (2.0 * spacing)
        longitudinal_operator_outputs: dict[str, Any] = {
            "time_centered_theta": midpoint_state["theta"].copy(),
            "backward_shift_p_previous": np.roll(previous_state["p"], 1),
            "backward_shift_p_current": np.roll(current_state["p"], 1),
            "backward_shift_grad_theta_midpoint": np.roll(
                midpoint_obs["grad_theta"], 1
            ),
            "grad_theta_midpoint_registered": midpoint_obs["grad_theta"].copy(),
            "forward_wilson_matrix": forward_matrix.copy(),
            "wilson_r": float(evolution.WILSON_R),
            "periodic_shift_rule": "NUMPY_ROLL_AXIS0",
            "time_centering_rule": "ARITHMETIC_MIDPOINT",
        }
        recomputed_grad = np.zeros(lattice_size, dtype=np.float64)
        for sigma, species in ((1, "psi_plus"), (-1, "psi_minus")):
            psi = midpoint_state[species]
            next_psi = np.roll(psi, -1, axis=0)
            gauge_phase = np.exp(
                1j * sigma * charge * midpoint_state["theta"]
            )
            transported = gauge_phase[:, None] * next_psi
            bilinear = np.einsum(
                "ni,ij,nj->n", psi.conj(), forward_matrix, transported
            )
            contribution = 2.0 * spacing * np.real(
                1j * sigma * charge * bilinear
            )
            recomputed_grad += contribution
            longitudinal_operator_outputs[f"{species}_next_periodic"] = (
                next_psi.copy()
            )
            longitudinal_operator_outputs[f"{species}_gauge_phase"] = (
                gauge_phase.copy()
            )
            longitudinal_operator_outputs[f"{species}_forward_transport"] = (
                transported.copy()
            )
            longitudinal_operator_outputs[f"{species}_link_bilinear"] = (
                bilinear.copy()
            )
            longitudinal_operator_outputs[f"{species}_grad_contribution"] = (
                contribution.copy()
            )
        longitudinal_operator_outputs["grad_theta_midpoint_recomputed"] = (
            recomputed_grad
        )
        longitudinal_operator_outputs["grad_theta_recomputation_byte_identical"] = (
            recomputed_grad.tobytes(order="C")
            == midpoint_obs["grad_theta"].tobytes(order="C")
        )
        raw_events["discrete_closure"].append(
            {
                "step": step_index,
                "time": step_index * effective_dt,
                "operator_inputs": {
                    "p_previous": previous_state["p"].copy(),
                    "p_current": current_state["p"].copy(),
                    "rho_previous": previous_obs["rho"].copy(),
                    "rho_current": current_obs["rho"].copy(),
                    "grad_theta_midpoint": midpoint_obs["grad_theta"].copy(),
                    "a": spacing,
                    "dt": effective_dt,
                },
                "actual_discrete_operator_outputs": longitudinal_operator_outputs,
                **{
                    key: value.copy() if isinstance(value, np.ndarray) else value
                    for key, value in closure.items()
                },
            }
        )

    trajectory_projection = physical_trajectory_projection(physical_snapshots)
    payload: dict[str, Any] = {
        "schema_id": RUN_ROLE_PAYLOAD_SCHEMA_ID,
        "implementation_id": IMPLEMENTATION_ID,
        "historical_evolution_module": HISTORICAL_EVOLUTION_MODULE,
        "historical_pack_module": HISTORICAL_PACK_MODULE,
        "bound_source_sha256": dict(BOUND_SOURCE_SHA256),
        "role_id": str(role_id),
        "row_id": str(row_copy["row_id"]),
        "instrumentation_enabled": instrumentation_enabled,
        "model": "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
        "configuration": {
            "N": lattice_size,
            "a": spacing,
            "requested_dt": requested_dt,
            "effective_dt": effective_dt,
            "duration": final_time,
            "steps": steps,
            "solver_tolerance": requested_tolerance,
            "max_iterations": int(max_iterations),
            "mass": mass,
            "charge": charge,
            "row": row_copy,
        },
        "initial_state_reconstruction": reconstruction,
        "times": np.asarray(times, dtype=np.float64),
        "physical_trajectory": trajectory_projection,
        "physical_trajectory_sha256": physical_trajectory_sha256(
            list(trajectory_projection)
        ),
        "all_steps_converged": all_steps_converged,
        "maximum_iterations_used": maximum_iterations_used,
        "maximum_solver_residual": maximum_solver_residual,
        "raw_events": raw_events,
        "metrics": (
            _metric_summaries_from_events(raw_events, metric_configuration)
            if instrumentation_enabled
            else None
        ),
    }
    validation_errors = validate_run_role_payload(payload)
    if validation_errors:
        raise ValueError(f"invalid in-memory role payload: {validation_errors[0]}")
    return payload


def validate_run_role_payload(payload: Mapping[str, Any]) -> list[str]:
    """Validate the in-memory schema returned by ``run_role_in_memory``."""

    errors: list[str] = []
    required = {
        "schema_id",
        "implementation_id",
        "role_id",
        "row_id",
        "instrumentation_enabled",
        "configuration",
        "times",
        "physical_trajectory",
        "physical_trajectory_sha256",
        "raw_events",
        "metrics",
    }
    missing = sorted(required - set(payload))
    if missing:
        return [f"MISSING_FIELD:{missing[0]}"]
    if payload["schema_id"] != RUN_ROLE_PAYLOAD_SCHEMA_ID:
        errors.append("SCHEMA_ID_MISMATCH")
    if payload["implementation_id"] != IMPLEMENTATION_ID:
        errors.append("IMPLEMENTATION_ID_MISMATCH")
    try:
        projection = _finite_float64_array(
            payload["physical_trajectory"], "physical_trajectory", ndim=2
        )
        if projection.shape[1] % PACKED_COMPONENTS_PER_SITE != 0:
            errors.append("PHYSICAL_TRAJECTORY_PACKED_WIDTH_INVALID")
        actual_hash = physical_trajectory_sha256(list(projection))
        if actual_hash != payload["physical_trajectory_sha256"]:
            errors.append("PHYSICAL_TRAJECTORY_HASH_MISMATCH")
        times = _finite_float64_array(payload["times"], "times", ndim=1)
        if times.size != projection.shape[0]:
            errors.append("TIME_TRAJECTORY_LENGTH_MISMATCH")
    except (TypeError, ValueError):
        errors.append("PHYSICAL_TRAJECTORY_SCHEMA_INVALID")
        projection = None
    configuration = payload["configuration"]
    if not isinstance(configuration, Mapping) or "steps" not in configuration:
        errors.append("CONFIGURATION_SCHEMA_INVALID")
        steps = None
    else:
        steps = int(configuration["steps"])
        if projection is not None and projection.shape[0] != steps + 1:
            errors.append("PHYSICAL_TRAJECTORY_STEP_CLOSURE_MISMATCH")
    enabled = payload["instrumentation_enabled"]
    if type(enabled) is not bool:
        errors.append("INSTRUMENTATION_FLAG_INVALID")
    elif enabled:
        events = payload["raw_events"]
        if not isinstance(events, Mapping):
            errors.append("INSTRUMENTED_RAW_EVENTS_MISSING")
        else:
            if set(events) != set(MANDATORY_INSTRUMENTED_EVENT_FAMILIES):
                errors.append("INSTRUMENTED_EVENT_FAMILY_CLOSURE_MISMATCH")
            elif steps is not None and any(
                not isinstance(events[family], list) or len(events[family]) != steps
                for family in MANDATORY_INSTRUMENTED_EVENT_FAMILIES
            ):
                errors.append("INSTRUMENTED_EVENT_STEP_CLOSURE_MISMATCH")
        metrics = payload["metrics"]
        if not isinstance(metrics, Mapping) or set(metrics) != {
            "exchange_conditioning",
            "block_dominance",
            "discrete_closure",
            "distributed_accumulation",
        }:
            errors.append("CLASSIFIER_METRIC_FAMILY_CLOSURE_MISMATCH")
    else:
        if payload["raw_events"] is not None:
            errors.append("NONINSTRUMENTED_CONTROL_HAS_RAW_EVENTS")
        if payload["metrics"] is not None:
            errors.append("NONINSTRUMENTED_CONTROL_HAS_MECHANISM_METRICS")
    return errors


def canonical_json_bytes(value: Any) -> bytes:
    """Serialize a JSON-compatible value deterministically and reject NaN/Inf."""

    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _canonical_storage_array(value: np.ndarray) -> np.ndarray:
    array = np.asarray(value)
    if array.dtype.hasobject:
        raise TypeError("object arrays are forbidden in deterministic payloads")
    if array.dtype.kind not in "biufc":
        raise TypeError(f"unsupported deterministic array dtype {array.dtype}")
    if array.dtype.kind in "fc" and not np.all(np.isfinite(array)):
        raise ValueError("nonfinite arrays are forbidden in deterministic payloads")
    dtype = array.dtype.newbyteorder("<")
    return np.ascontiguousarray(array.astype(dtype, copy=False))


def _extract_payload_arrays(
    value: Any,
    arrays: dict[str, np.ndarray],
    registry: list[dict[str, Any]],
) -> Any:
    if isinstance(value, np.ndarray):
        array_id = f"array_{len(arrays):06d}"
        array = _canonical_storage_array(value)
        arrays[array_id] = array
        registry.append(
            {
                "array_id": array_id,
                "dtype": array.dtype.str,
                "shape": list(array.shape),
                "raw_c_order_sha256": hashlib.sha256(
                    array.tobytes(order="C")
                ).hexdigest(),
            }
        )
        return {"$npz_array": array_id}
    if isinstance(value, np.generic):
        return _extract_payload_arrays(value.item(), arrays, registry)
    if isinstance(value, Mapping):
        if any(not isinstance(key, str) for key in value):
            raise TypeError("deterministic payload mappings require string keys")
        return {
            key: _extract_payload_arrays(value[key], arrays, registry)
            for key in sorted(value)
        }
    if isinstance(value, (list, tuple)):
        return [_extract_payload_arrays(item, arrays, registry) for item in value]
    if value is None or isinstance(value, (str, bool, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("nonfinite scalars are forbidden in deterministic payloads")
        return value
    raise TypeError(f"unsupported deterministic payload type {type(value).__name__}")


def deterministic_npz_bytes(arrays: Mapping[str, np.ndarray]) -> bytes:
    """Create timestamp-independent, sorted, uncompressed NPZ bytes."""

    output = io.BytesIO()
    with zipfile.ZipFile(
        output,
        mode="w",
        compression=zipfile.ZIP_STORED,
        allowZip64=True,
    ) as archive:
        for array_id in sorted(arrays):
            invalid_character = any(
                character not in "abcdefghijklmnopqrstuvwxyz_0123456789"
                for character in array_id
            )
            if not array_id or invalid_character:
                raise ValueError(f"invalid deterministic array ID {array_id!r}")
            array = _canonical_storage_array(arrays[array_id])
            array_bytes = io.BytesIO()
            np.lib.format.write_array(
                array_bytes,
                array,
                version=(2, 0),
                allow_pickle=False,
            )
            info = zipfile.ZipInfo(
                filename=f"{array_id}.npy",
                date_time=(1980, 1, 1, 0, 0, 0),
            )
            info.compress_type = zipfile.ZIP_STORED
            info.create_system = 3
            info.external_attr = 0o600 << 16
            archive.writestr(info, array_bytes.getvalue())
    return output.getvalue()


def serialize_run_role_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    """Return deterministic JSON metadata and NPZ bytes for a role payload."""

    validation_errors = validate_run_role_payload(payload)
    if validation_errors:
        raise ValueError(f"invalid role payload: {validation_errors[0]}")
    arrays: dict[str, np.ndarray] = {}
    registry: list[dict[str, Any]] = []
    projected_payload = _extract_payload_arrays(payload, arrays, registry)
    npz_bytes = deterministic_npz_bytes(arrays)
    envelope = {
        "schema_id": RUN_PAYLOAD_JSON_SCHEMA_ID,
        "npz_schema_id": RUN_PAYLOAD_NPZ_SCHEMA_ID,
        "output_schema_version": OUTPUT_SCHEMA_VERSION,
        "implementation_id": IMPLEMENTATION_ID,
        "role_id": payload["role_id"],
        "array_registry": registry,
        "npz_sha256": hashlib.sha256(npz_bytes).hexdigest(),
        "payload": projected_payload,
    }
    json_bytes = canonical_json_bytes(envelope)
    return {
        "json_bytes": json_bytes,
        "npz_bytes": npz_bytes,
        "json_sha256": hashlib.sha256(json_bytes).hexdigest(),
        "npz_sha256": hashlib.sha256(npz_bytes).hexdigest(),
        "array_count": len(arrays),
    }


def _write_bytes_exclusive(path: Path, payload: bytes) -> None:
    if not path.parent.is_dir():
        raise FileNotFoundError(f"output parent does not exist: {path.parent}")
    with path.open("xb") as handle:
        handle.write(payload)
        handle.flush()


def write_run_role_payload_once(
    payload: Mapping[str, Any],
    json_path: str | Path,
    npz_path: str | Path,
) -> dict[str, Any]:
    """Write a role payload once, refusing either pre-existing destination."""

    json_target = Path(json_path)
    npz_target = Path(npz_path)
    if json_target.resolve() == npz_target.resolve():
        raise ValueError("JSON and NPZ paths must differ")
    if json_target.exists() or npz_target.exists():
        raise FileExistsError("no-overwrite contract: role payload destination exists")
    serialized = serialize_run_role_payload(payload)
    # Precompute both payloads before the first exclusive write.  If an external
    # failure occurs after the first write, the partial evidence is intentionally
    # retained; the matrix root then prevents any retry.
    _write_bytes_exclusive(json_target, serialized["json_bytes"])
    _write_bytes_exclusive(npz_target, serialized["npz_bytes"])
    return {
        "json_relative_name": json_target.name,
        "npz_relative_name": npz_target.name,
        "json_sha256": serialized["json_sha256"],
        "npz_sha256": serialized["npz_sha256"],
        "array_count": serialized["array_count"],
    }


def directory_tree_sha256(root: str | Path) -> str:
    """Compute a deterministic read-only digest of every file below ``root``."""

    directory = Path(root)
    if not directory.is_dir():
        raise FileNotFoundError(f"digest root is not a directory: {directory}")
    digest = hashlib.sha256()
    digest.update(b"R13-MECHANISM-DIRECTORY-TREE-v0\x00")
    files = sorted(
        (path for path in directory.rglob("*") if path.is_file()),
        key=lambda path: path.relative_to(directory).as_posix(),
    )
    for path in files:
        relative = path.relative_to(directory).as_posix().encode("utf-8")
        contents = path.read_bytes()
        digest.update(struct.pack("<Q", len(relative)))
        digest.update(relative)
        digest.update(struct.pack("<Q", len(contents)))
        digest.update(hashlib.sha256(contents).digest())
    return digest.hexdigest()


def _paths_overlap(left: Path, right: Path) -> bool:
    left_resolved = left.resolve()
    right_resolved = right.resolve()
    return (
        left_resolved == right_resolved
        or left_resolved in right_resolved.parents
        or right_resolved in left_resolved.parents
    )


def _role_metric_configuration(
    metric_configuration_template: Mapping[str, Any],
    tolerance: float,
) -> dict[str, Any]:
    configuration = dict(metric_configuration_template)
    exact_scales = {
        block_id: float(tolerance) for block_id in PACKED_RESIDUAL_BLOCK_IDS
    }
    exact_floors = {block_id: GAMMA64 for block_id in PACKED_RESIDUAL_BLOCK_IDS}
    if "block_scales" in configuration and configuration["block_scales"] != exact_scales:
        raise ValueError("frozen block scales must equal the role solver tolerance")
    if "block_floors" in configuration and configuration["block_floors"] != exact_floors:
        raise ValueError("frozen block floors must equal gamma64")
    if "epsilon_dominance" in configuration and float(
        configuration["epsilon_dominance"]
    ) != GAMMA64:
        raise ValueError("frozen epsilon_dominance must equal gamma64")
    configuration["block_scales"] = exact_scales
    configuration["block_floors"] = exact_floors
    configuration["epsilon_dominance"] = GAMMA64
    _validate_metric_configuration(configuration)
    return configuration


def validate_exact_run_matrix(run_matrix: Sequence[Mapping[str, Any]]) -> list[str]:
    """Validate exact six-role identity, order, pairing, and tolerance structure."""

    errors: list[str] = []
    if isinstance(run_matrix, (str, bytes, bytearray)) or not isinstance(
        run_matrix, Sequence
    ):
        return ["RUN_MATRIX_NOT_SEQUENCE"]
    if len(run_matrix) != len(EXACT_MATRIX_RUN_IDS):
        return ["RUN_MATRIX_COUNT_MISMATCH"]
    if any(not isinstance(record, Mapping) for record in run_matrix):
        return ["RUN_MATRIX_RECORD_NOT_MAPPING"]
    observed_ids = [str(record.get("run_id")) for record in run_matrix]
    if observed_ids != EXACT_MATRIX_RUN_IDS:
        errors.append("RUN_MATRIX_ID_OR_ORDER_MISMATCH")
        return errors
    required = {
        "run_id",
        "row",
        "n",
        "dt",
        "duration",
        "tolerance",
        "max_iterations",
        "instrumentation_enabled",
        "json_relative_output_path",
        "npz_relative_output_path",
    }
    for record in run_matrix:
        missing = sorted(required - set(record))
        if missing:
            errors.append(f"RUN_MATRIX_FIELD_MISSING:{record['run_id']}:{missing[0]}")
            continue
        run_id = str(record["run_id"])
        enabled = record["instrumentation_enabled"]
        expected_enabled = run_id.endswith(":INSTRUMENTED")
        if type(enabled) is not bool or enabled != expected_enabled:
            errors.append(f"RUN_MATRIX_INSTRUMENTATION_FLAG_MISMATCH:{run_id}")
        row = record["row"]
        expected_row_id = EXPECTED_ROW_ID_BY_RUN_ID[run_id]
        if not isinstance(row, Mapping) or dict(row) != EXPECTED_ROW_PARAMETERS[
            expected_row_id
        ]:
            errors.append(f"RUN_MATRIX_ROW_ID_MISMATCH:{run_id}")
        if type(record["n"]) is not int or record["n"] != EXPECTED_EXPERIMENT_NUMERICS["n"]:
            errors.append(f"RUN_MATRIX_N_MISMATCH:{run_id}")
        if record["dt"] != EXPECTED_EXPERIMENT_NUMERICS["dt"]:
            errors.append(f"RUN_MATRIX_DT_MISMATCH:{run_id}")
        if record["duration"] != EXPECTED_EXPERIMENT_NUMERICS["duration"]:
            errors.append(f"RUN_MATRIX_DURATION_MISMATCH:{run_id}")
        if (
            type(record["max_iterations"]) is not int
            or record["max_iterations"]
            != EXPECTED_EXPERIMENT_NUMERICS["max_iterations"]
        ):
            errors.append(f"RUN_MATRIX_ITERATION_CAP_MISMATCH:{run_id}")
        if record["tolerance"] != EXPECTED_TOLERANCE_BY_RUN_ID[run_id]:
            errors.append(f"RUN_MATRIX_TOLERANCE_MISMATCH:{run_id}")
        expected_paths = EXPECTED_OUTPUT_PATHS_BY_RUN_ID[run_id]
        for path_field in (
            "json_relative_output_path",
            "npz_relative_output_path",
        ):
            if record[path_field] != expected_paths[path_field]:
                errors.append(
                    f"RUN_MATRIX_OUTPUT_PATH_MISMATCH:{run_id}:{path_field}"
                )
    pair_indexes = ((0, 1), (2, 3), (4, 5))
    comparison_fields = ("row", "n", "dt", "duration", "tolerance", "max_iterations")
    for instrumented_index, control_index in pair_indexes:
        instrumented = run_matrix[instrumented_index]
        control = run_matrix[control_index]
        for field in comparison_fields:
            if instrumented.get(field) != control.get(field):
                errors.append(
                    f"RUN_MATRIX_PAIR_MISMATCH:{instrumented['run_id']}:{field}"
                )
    try:
        loose_tolerance = float(run_matrix[0]["tolerance"])
        tight_tolerance = float(run_matrix[2]["tolerance"])
        neighbor_tolerance = float(run_matrix[4]["tolerance"])
        if not tight_tolerance < loose_tolerance:
            errors.append("RUN_MATRIX_TIGHT_TOLERANCE_NOT_STRICTLY_TIGHTER")
        if neighbor_tolerance != loose_tolerance:
            errors.append("RUN_MATRIX_NEIGHBOR_NOT_AT_LOOSE_TOLERANCE")
    except (KeyError, TypeError, ValueError):
        errors.append("RUN_MATRIX_TOLERANCE_SCHEMA_INVALID")
    return errors


def assemble_classifier_metrics(
    payload_by_run_id: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Assemble the three instrumented summaries in classifier role schema."""

    result = {
        family: {}
        for family in (
            "exchange_conditioning",
            "block_dominance",
            "discrete_closure",
            "distributed_accumulation",
        )
    }
    for run_id, classifier_role in CLASSIFIER_ROLE_BY_INSTRUMENTED_RUN_ID.items():
        payload = payload_by_run_id.get(run_id)
        if not isinstance(payload, Mapping) or not isinstance(payload.get("metrics"), Mapping):
            raise ValueError(f"missing instrumented metrics for {run_id}")
        for family in result:
            result[family][classifier_role] = payload["metrics"][family]
    return result


def execute_exact_matrix_once(
    run_matrix: Sequence[Mapping[str, Any]],
    metric_configuration_template: Mapping[str, Any],
    output_root: str | Path,
    canonical_output_root: str | Path,
) -> dict[str, Any]:
    """Execute and persist the exact six-role matrix once, with no retry.

    This function is callable only; nothing in this module invokes it.  The new
    output root must not exist and must not overlap the canonical output root.
    An exclusive start marker is written before the first role.  Any exception
    leaves that root and all partial evidence in place, so another call refuses
    to retry or overwrite the attempt.
    """

    matrix_errors = validate_exact_run_matrix(run_matrix)
    if matrix_errors:
        raise ValueError(f"invalid exact run matrix: {matrix_errors[0]}")
    if platform.python_version() != EXPECTED_PYTHON_VERSION:
        raise RuntimeError("Python version does not match the frozen environment")
    if np.__version__ != EXPECTED_NUMPY_VERSION:
        raise RuntimeError("NumPy version does not match the frozen environment")
    environment_mismatches = {
        key: os.environ.get(key)
        for key, expected in REQUIRED_EXECUTION_ENVIRONMENT.items()
        if os.environ.get(key) != expected
    }
    if environment_mismatches:
        raise RuntimeError(
            "execution environment does not match frozen values: "
            + ",".join(sorted(environment_mismatches))
        )
    output = Path(output_root)
    canonical = Path(canonical_output_root)
    repo_root = Path(__file__).resolve().parents[3]
    expected_output = (
        repo_root / EXPECTED_EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    ).resolve()
    if output.resolve() != expected_output:
        raise ValueError("output_root is not the frozen mechanism experiment root")
    if not canonical.is_dir():
        raise FileNotFoundError("canonical_output_root must be an existing directory")
    if _paths_overlap(output, canonical):
        raise ValueError("mechanism output root must be separate from canonical output root")
    if output.exists():
        raise FileExistsError("no-retry contract: mechanism output root already exists")
    if not output.parent.is_dir():
        raise FileNotFoundError("mechanism output parent must already exist")

    expected_canonical = (
        repo_root / EXPECTED_CANONICAL_ROOT_RELATIVE_PATH
    ).resolve()
    if canonical.resolve() != expected_canonical:
        raise ValueError("canonical_output_root is not the frozen canonical root")
    implementation_binding = source_binding_report(repo_root)
    if implementation_binding["all_passed"] is not True:
        raise RuntimeError("historical implementation source binding failed")
    canonical_digest_before = directory_tree_sha256(canonical)
    if canonical_digest_before != EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256:
        raise RuntimeError("stale or mutated canonical directory-tree custody")
    output.mkdir(exist_ok=False)
    start_marker = {
        "schema_id": MATRIX_RESULT_SCHEMA_ID,
        "status": "EXECUTION_STARTED_NO_RETRY",
        "implementation_id": IMPLEMENTATION_ID,
        "exact_run_ids": EXACT_MATRIX_RUN_IDS,
        "historical_implementation_binding": implementation_binding,
        "canonical_output_root": str(canonical.resolve()),
        "canonical_digest_before": canonical_digest_before,
        "canonical_directory_tree_digest_domain": (
            EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256_DOMAIN
        ),
        "canonical_authority_inventory_digest": EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_authority_inventory_digest_domain": (
            EXPECTED_CANONICAL_ROOT_DIGEST_DOMAIN
        ),
        "no_overwrite": True,
        "no_retry": True,
    }
    _write_bytes_exclusive(
        output / "EXECUTION-STARTED.json", canonical_json_bytes(start_marker)
    )

    payload_by_run_id: dict[str, Mapping[str, Any]] = {}
    custody_records: list[dict[str, Any]] = []
    for index, record in enumerate(run_matrix):
        run_id = str(record["run_id"])
        role_metric_configuration = _role_metric_configuration(
            metric_configuration_template, float(record["tolerance"])
        )
        # Exactly one call, with no retry branch.
        payload = run_role_in_memory(
            record["row"],
            run_id,
            int(record["n"]),
            float(record["dt"]),
            float(record["duration"]),
            float(record["tolerance"]),
            int(record["max_iterations"]),
            instrumentation_enabled=bool(record["instrumentation_enabled"]),
            metric_configuration=role_metric_configuration,
        )
        payload_by_run_id[run_id] = payload
        json_target = repo_root / str(record["json_relative_output_path"])
        npz_target = repo_root / str(record["npz_relative_output_path"])
        if json_target.parent.resolve() != output.resolve():
            raise ValueError("JSON role output escapes the frozen mechanism root")
        if npz_target.parent.resolve() != output.resolve():
            raise ValueError("NPZ role output escapes the frozen mechanism root")
        write_record = write_run_role_payload_once(
            payload,
            json_target,
            npz_target,
        )
        custody_records.append(
            {
                "run_id": run_id,
                "execution_ordinal": index + 1,
                "json_relative_output_path": record[
                    "json_relative_output_path"
                ],
                "npz_relative_output_path": record[
                    "npz_relative_output_path"
                ],
                "physical_trajectory_sha256": payload[
                    "physical_trajectory_sha256"
                ],
                **write_record,
            }
        )

    pair_records: list[dict[str, Any]] = []
    for instrumented_index, control_index in ((0, 1), (2, 3), (4, 5)):
        instrumented_id = EXACT_MATRIX_RUN_IDS[instrumented_index]
        control_id = EXACT_MATRIX_RUN_IDS[control_index]
        comparison = compare_physical_trajectories(
            list(payload_by_run_id[instrumented_id]["physical_trajectory"]),
            list(payload_by_run_id[control_id]["physical_trajectory"]),
        )
        pair_records.append(
            {
                "instrumented_run_id": instrumented_id,
                "control_run_id": control_id,
                **comparison,
            }
        )

    canonical_digest_after = directory_tree_sha256(canonical)
    canonical_unchanged = canonical_digest_after == canonical_digest_before
    all_pairs_byte_identical = all(
        record["byte_identical"] for record in pair_records
    )
    classifier_metrics = assemble_classifier_metrics(payload_by_run_id)
    result = {
        "schema_id": MATRIX_RESULT_SCHEMA_ID,
        "output_schema_version": OUTPUT_SCHEMA_VERSION,
        "status": (
            "BLOCKED_CANONICAL_OUTPUT_MUTATION"
            if not canonical_unchanged
            else "BLOCKED_INSTRUMENTATION_PERTURBATION"
            if not all_pairs_byte_identical
            else "EXECUTION_COMPLETED_ONCE"
        ),
        "implementation_id": IMPLEMENTATION_ID,
        "historical_implementation_binding": implementation_binding,
        "exact_run_ids": EXACT_MATRIX_RUN_IDS,
        "execution_count_by_run_id": {
            run_id: 1 for run_id in EXACT_MATRIX_RUN_IDS
        },
        "run_custody": custody_records,
        "instrumentation_nonperturbation_pairs": pair_records,
        "all_pairs_byte_identical": all_pairs_byte_identical,
        "mechanism_classification_allowed": (
            canonical_unchanged and all_pairs_byte_identical
        ),
        "canonical_digest_before": canonical_digest_before,
        "canonical_digest_after": canonical_digest_after,
        "canonical_directory_tree_digest_domain": (
            EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256_DOMAIN
        ),
        "canonical_authority_inventory_digest": EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_authority_inventory_digest_domain": (
            EXPECTED_CANONICAL_ROOT_DIGEST_DOMAIN
        ),
        "canonical_digest_unchanged": canonical_unchanged,
        "classifier_metrics": classifier_metrics,
        "claim_ceiling": (
            "NUMERICAL_MECHANISM_EVIDENCE_ONLY; no robustness reclassification, "
            "materiality evaluation, physical claim, or E-REPRO"
        ),
    }
    result_bytes = canonical_json_bytes(result)
    _write_bytes_exclusive(output / "MATRIX-RESULT.json", result_bytes)
    if not canonical_unchanged:
        raise RuntimeError("canonical output digest changed during mechanism execution")
    return result


def source_binding_report(repo_root: str | Path) -> dict[str, Any]:
    """Read and hash bound historical sources without modifying them."""

    root = Path(repo_root)
    records: list[dict[str, Any]] = []
    for relative_path, expected_sha256 in BOUND_SOURCE_SHA256.items():
        path = root / relative_path
        actual_sha256 = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        records.append(
            {
                "relative_path": relative_path,
                "expected_sha256": expected_sha256,
                "actual_sha256": actual_sha256,
                "passed": actual_sha256 == expected_sha256,
            }
        )
    return {
        "implementation_id": IMPLEMENTATION_ID,
        "bindings": records,
        "all_passed": all(record["passed"] for record in records),
    }


def self_validate() -> dict[str, bool]:
    """Run concise deterministic unit-level checks; no evolution is executed."""

    n = 3
    packed = np.arange(PACKED_COMPONENTS_PER_SITE * n, dtype=np.float64)
    blocks = split_packed_residual(packed, n, copy=False)
    block_lengths = [blocks[block_id].size for block_id in PACKED_RESIDUAL_BLOCK_IDS]
    layout_passed = block_lengths == [n, n, n, n, n, n, 8 * n, 8 * n]
    coverage_passed = sum(block_lengths) == packed.size

    p0 = np.array([0.2, -0.1, 0.3], dtype=np.float64)
    rho0 = np.array([0.04, -0.02, 0.01], dtype=np.float64)
    rho1 = np.array([0.03, -0.015, 0.005], dtype=np.float64)
    grad = np.array([0.08, -0.06, 0.02], dtype=np.float64)
    defect = np.array([2.0e-10, -1.0e-10, 3.0e-10], dtype=np.float64)
    dt = 0.01
    a = 0.25
    p1 = p0 - dt * grad + defect
    closure = discrete_maxwell_continuity_closure(p0, p1, rho0, rho1, grad, a, dt)
    closure_passed = bool(
        np.all(
            np.abs(np.asarray(closure["closure_q"]))
            <= np.asarray(closure["roundoff_bound"])
        )
    )

    exchange = exchange_conditioning_series(np.zeros(2), np.zeros(2))
    zero_exchange_passed = bool(np.all(np.asarray(exchange["kappa"]) == 0.0))

    trajectory = [packed, packed + 1.0]
    same = compare_physical_trajectories(trajectory, trajectory)
    different = compare_physical_trajectories(trajectory, [packed, packed + 2.0])
    trajectory_passed = bool(same["byte_identical"] and not different["byte_identical"])
    checks = {
        "packed_block_layout_passed": layout_passed,
        "packed_block_coverage_passed": coverage_passed,
        "discrete_closure_identity_within_gamma32_bound": closure_passed,
        "zero_exchange_kappa_is_zero": zero_exchange_passed,
        "physical_trajectory_hash_and_equality_passed": trajectory_passed,
    }
    if not all(checks.values()):
        raise AssertionError(f"instrumentation support self-validation failed: {checks}")
    return checks


__all__ = [
    "BLOCK_REGISTRY",
    "BOUND_SOURCE_SHA256",
    "DISCRETE_CLOSURE_CONTRACT",
    "DISCRETE_CLOSURE_BOUND_FORMULA",
    "DISCRETE_CLOSURE_Q_FORMULA",
    "EXACT_MATRIX_RUN_IDS",
    "EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256",
    "EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256_DOMAIN",
    "EXPECTED_CANONICAL_ROOT_DIGEST",
    "EXPECTED_CANONICAL_ROOT_DIGEST_DOMAIN",
    "EXPECTED_CANONICAL_ROOT_RELATIVE_PATH",
    "EXPECTED_EXPERIMENT_NUMERICS",
    "EXPECTED_EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH",
    "EXPECTED_OUTPUT_PATHS_BY_RUN_ID",
    "EXPECTED_ROW_PARAMETERS",
    "EXPECTED_TOLERANCE_BY_RUN_ID",
    "EXCHANGE_CONDITIONING_FORMULA",
    "EXPECTED_NUMPY_VERSION",
    "EXPECTED_PYTHON_VERSION",
    "FLOAT64_UNIT_ROUNDOFF",
    "GAMMA32",
    "GAMMA64",
    "HISTORICAL_EVOLUTION_MODULE",
    "HISTORICAL_PACK_MODULE",
    "IMPLEMENTATION_ID",
    "MATRIX_RESULT_SCHEMA_ID",
    "LONGITUDINAL_BLOCK_IDS",
    "MANDATORY_INSTRUMENTED_EVENT_FAMILIES",
    "OBSERVABLE_IDS",
    "OUTPUT_SCHEMA_VERSION",
    "PACKED_COMPONENTS_PER_SITE",
    "PACKED_RESIDUAL_BLOCK_IDS",
    "RUN_ROLE_PAYLOAD_SCHEMA_ID",
    "REQUIRED_EXECUTION_ENVIRONMENT",
    "RUN_PAYLOAD_JSON_SCHEMA_ID",
    "RUN_PAYLOAD_NPZ_SCHEMA_ID",
    "SCRIPT_RELATIVE_PATH",
    "block_dominance_shares",
    "canonical_json_bytes",
    "compare_physical_trajectories",
    "discrete_maxwell_continuity_closure",
    "directory_tree_sha256",
    "exchange_conditioning_series",
    "gamma_n",
    "implicit_midpoint_equation_defect",
    "infer_lattice_size",
    "normalize_block_residuals",
    "packed_residual_block_maxima",
    "packed_residual_block_slices",
    "physical_trajectory_projection",
    "physical_trajectory_sha256",
    "picard_midpoint_step_with_observer",
    "assemble_classifier_metrics",
    "deterministic_npz_bytes",
    "execute_exact_matrix_once",
    "run_role_in_memory",
    "self_validate",
    "source_binding_report",
    "split_packed_residual",
    "summarize_block_dominance",
    "summarize_discrete_closure",
    "summarize_distributed_accumulation",
    "summarize_exchange_conditioning",
    "serialize_run_role_payload",
    "validate_exact_run_matrix",
    "validate_run_role_payload",
    "write_run_role_payload_once",
]
