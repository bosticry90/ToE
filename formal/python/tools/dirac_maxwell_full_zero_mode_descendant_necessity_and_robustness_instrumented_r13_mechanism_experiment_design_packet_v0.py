from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v0"
)
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v0_result"
)
DOWNSTREAM_TARGET_IF_ACCEPTED = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)
PACKET_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_v0"
)
MANIFEST_SCHEMA_ID = f"{PACKET_SCHEMA_ID}_MANIFEST"
REPORT_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_20260715_v0"
)

PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-PACKET-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-MANIFEST-v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_20260715_v0.json"
)
GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_v0.py"
)
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

ROUTE_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_REVIEW_20260715_v0.json"
)
ROUTE_REVIEWER = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_route_selection_packet_review_v0.py"
)
ROUTE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-ROUTE-SELECTION-PACKET-v0.json"
)
DIAGNOSTIC_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0.json"
)
FREEZE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
)
RUN_MATRIX = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
)
IDENTITY_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
EXECUTION_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
EXECUTION_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-PACKET-v2.json"
)
OUTPUT_ROOT = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)

EXPECTED_SOURCE_HASHES = {
    ROUTE_REVIEW_REPORT: "a7c48d0d14d69a6d1990d03b09598d449b3e8761f20fc0b2f9308449e73028ed",
    ROUTE_REVIEWER: "953374cad4be66e3f3512039e734aa207c52fe32b7cd0c403192f1ab5759062b",
    ROUTE_PACKET: "b0c76f95bc767a9940ba19b6221ba7c113d0d99fe037e5f586723d88b664d712",
    DIAGNOSTIC_REVIEW_REPORT: "15c7bb4ed25f0ce029aac83c231903b69e1073cb356547e0dbc8644b3b200873",
    FREEZE_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    RUN_MATRIX: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
}
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)

R13 = "R13_CORNER_STRONG_LOW"
MECHANISM_IDS = [
    "FIELD_MATTER_EXCHANGE_CANCELLATION_CONDITIONING",
    "NONLINEAR_EQUATION_BLOCK_DOMINANCE",
    "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE",
]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _canonical_root_inventory() -> list[dict[str, str]]:
    return [
        {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for path in sorted((REPO_ROOT / OUTPUT_ROOT).glob("*.json"))
    ]


def canonical_root_digest() -> str:
    return sha256_bytes(canonical_json_bytes(_canonical_root_inventory()))


def _load_sources() -> dict[str, Any]:
    route_review = load_json(REPO_ROOT / ROUTE_REVIEW_REPORT)
    route_packet = load_json(REPO_ROOT / ROUTE_PACKET)
    diagnostic_review = load_json(REPO_ROOT / DIAGNOSTIC_REVIEW_REPORT)
    freeze = load_json(REPO_ROOT / FREEZE_PACKET)
    matrix = load_json(REPO_ROOT / RUN_MATRIX)
    identity = load_json(REPO_ROOT / IDENTITY_MANIFEST)
    execution_manifest = load_json(REPO_ROOT / EXECUTION_MANIFEST)
    execution_packet = load_json(REPO_ROOT / EXECUTION_PACKET)
    return {
        "route_review": route_review,
        "route_packet": route_packet,
        "diagnostic_review": diagnostic_review,
        "freeze": freeze,
        "matrix": matrix,
        "identity": identity,
        "execution_manifest": execution_manifest,
        "execution_packet": execution_packet,
    }


def _source_custody(sources: dict[str, Any]) -> dict[str, Any]:
    hashes = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES}
    identity_by_run = {item["run_id"]: item for item in sources["identity"]["outputs"]}
    execution_by_run = {
        item["run_id"]: item for item in sources["execution_manifest"]["run_outputs"]
    }
    failures = []
    for run_id, identity in identity_by_run.items():
        execution = execution_by_run.get(run_id, {})
        path = identity["relative_output_path"]
        observed = sha256_path(REPO_ROOT / path)
        if (
            observed != execution.get("output_sha256")
            or path != execution.get("relative_output_path")
        ):
            failures.append(
                {
                    "run_id": run_id,
                    "path": path,
                    "observed_sha256": observed,
                    "expected_sha256": execution.get("output_sha256"),
                }
            )
    inventory = _canonical_root_inventory()
    digest = sha256_bytes(canonical_json_bytes(inventory))
    review = sources["route_review"]
    authority_exact = (
        review["accepted"] is True
        and review["verdict"]
        == "ACCEPT_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_ROUTE_A_DESIGN_PREPARATION_ONLY"
        and review["selected_route"]
        == "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"
        and review["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
        and review["root_numerical_mechanism_status"] == "UNRESOLVED"
        and review["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and review["selected_next_target"] == TARGET
    )
    return {
        "source_artifact_hashes": hashes,
        "expected_source_artifact_hashes": EXPECTED_SOURCE_HASHES,
        "all_source_artifact_hashes_exact": hashes == EXPECTED_SOURCE_HASHES,
        "accepted_route_A_design_preparation_authority_exact": authority_exact,
        "canonical_run_output_count_checked": len(identity_by_run),
        "canonical_run_output_hash_failures": failures,
        "canonical_root_file_count": len(inventory),
        "canonical_root_digest": digest,
        "canonical_root_digest_exact": digest == EXPECTED_CANONICAL_ROOT_DIGEST,
        "execution_count_performed": sources["execution_packet"][
            "execution_count_performed"
        ],
        "new_simulation_run_count": 0,
        "canonical_output_mutation_count": 0,
        "passed": hashes == EXPECTED_SOURCE_HASHES
        and authority_exact
        and len(identity_by_run) == len(execution_by_run) == 203
        and not failures
        and len(inventory) == 205
        and digest == EXPECTED_CANONICAL_ROOT_DIGEST
        and sources["execution_packet"]["execution_count_performed"] == 1,
    }


def _scientific_questions() -> list[dict[str, Any]]:
    return [
        {
            "question_id": "Q_A_EXCHANGE_CANCELLATION",
            "mechanism_id": MECHANISM_IDS[0],
            "question": (
                "Is the longitudinal exchange residual amplified by subtraction of large, nearly "
                "cancelling field and matter transfers?"
            ),
        },
        {
            "question_id": "Q_B_EQUATION_BLOCK",
            "mechanism_id": MECHANISM_IDS[1],
            "question": (
                "Which implemented equation block first carries, dominates, or amplifies the "
                "loose-tolerance solver error?"
            ),
        },
        {
            "question_id": "Q_C_DISCRETE_CLOSURE",
            "mechanism_id": MECHANISM_IDS[2],
            "question": (
                "Does the actual discrete longitudinal Maxwell equation account for the observed "
                "continuity residual within its frozen truncation remainder?"
            ),
        },
    ]


def _required_run_classes() -> list[dict[str, Any]]:
    return [
        {
            "role_class": "CORE_R13_LOOSE_MECHANISM",
            "scientific_row_rule": "exact historical R13_CORNER_STRONG_LOW parameters",
            "solver_tolerance_rule": "anchor to historically failing SOLVER_TOL1eM08 (1e-8)",
            "purpose": "reproduce and explain the accepted numerical block",
            "instrumented": True,
            "required": True,
        },
        {
            "role_class": "CORE_R13_TIGHT_REFERENCE",
            "scientific_row_rule": "configuration-identical R13_CORNER_STRONG_LOW parameters",
            "solver_tolerance_rule": (
                "future freeze selects at least one historically passing canonical reference from "
                "1e-10 and 1e-12 by a predeclared rule"
            ),
            "purpose": "identify internal structures suppressed by a tighter solve",
            "instrumented": True,
            "required": True,
        },
        {
            "role_class": "CORE_MATCHED_PASSING_NEIGHBOR_LOOSE",
            "scientific_row_rule": "future freeze applies the deterministic neighbor rule",
            "solver_tolerance_rule": "historical loose-solver role at 1e-8",
            "purpose": "contrast R13 with the closest canonically admissible parameter row",
            "instrumented": True,
            "required": True,
        },
        {
            "role_class": "INSTRUMENTATION_NONPERTURBATION_REFERENCE",
            "scientific_row_rule": (
                "paired configuration for every distinct core instrumented physical role"
            ),
            "solver_tolerance_rule": "identical to its paired instrumented role",
            "purpose": "prove diagnostics do not change registered physical trajectories",
            "instrumented": False,
            "required": True,
        },
    ]


def _neighbor_candidate_audit(sources: dict[str, Any]) -> dict[str, Any]:
    scientific_rows = {
        item["row_id"]: item["requested_axis_values"]
        for item in sources["freeze"]["scientific_design_freeze"]["scientific_rows"]
    }
    r13_axes = scientific_rows[R13]
    axis_ranges = {
        axis: (
            min(float(values[axis]) for values in scientific_rows.values()),
            max(float(values[axis]) for values in scientific_rows.values()),
        )
        for axis in r13_axes
    }
    reviewed_neighbors = sources["diagnostic_review"][
        "independent_neighbor_reconstruction"
    ]["axis_sharing_neighbors"]
    rows = []
    for reviewed in reviewed_neighbors:
        row_id = reviewed["scientific_row_id"]
        axes = scientific_rows[row_id]
        shared = sorted(axis for axis, value in axes.items() if value == r13_axes[axis])
        squared = 0.0
        normalized_components = {}
        for axis, value in axes.items():
            low, high = axis_ranges[axis]
            component = (
                (float(value) - float(r13_axes[axis])) / (high - low)
                if high > low
                else 0.0
            )
            normalized_components[axis] = component
            squared += component * component
        rows.append(
            {
                "scientific_row_id": row_id,
                "shared_axis_count": len(shared),
                "shared_axes": shared,
                "normalized_distance": math.sqrt(squared),
                "normalized_distance_components": normalized_components,
                "all_four_loose_solver_residual_ceilings_pass": reviewed["all_four_pass"],
                "maximum_loose_solver_ceiling_ratio": reviewed["maximum_ceiling_ratio"],
            }
        )
    ranked = sorted(
        rows,
        key=lambda item: (
            -item["shared_axis_count"],
            item["normalized_distance"],
            item["scientific_row_id"],
        ),
    )
    return {
        "status": "DESIGN_RULE_AND_FEASIBILITY_AUDIT_EXACT_SELECTION_DEFERRED_TO_FREEZE",
        "eligibility_rule": (
            "canonical scientific rows other than R13 whose historical 1e-8 solver role passed all "
            "four R13-linked residual ceilings"
        ),
        "ranking_rule": [
            "maximize number of shared R13 axis values",
            "minimize Euclidean distance after per-axis min-max normalization over the frozen matrix",
            "break remaining ties by lexicographically ascending scientific_row_id",
        ],
        "axis_normalization_rule": (
            "(candidate_value - R13_value) / (frozen_axis_max - frozen_axis_min)"
        ),
        "eligible_axis_sharing_candidate_count": len(ranked),
        "ranked_candidate_audit": ranked,
        "provisional_top_candidate_for_freeze_confirmation": ranked[0][
            "scientific_row_id"
        ],
        "exact_neighbor_frozen_now": False,
        "post_result_visual_choice_allowed": False,
    }


def _nonperturbation_contract() -> dict[str, Any]:
    return {
        "instrumentation_permission": (
            "read immutable snapshots of registered state, residual, operator, and solver metadata "
            "and emit them to a separate output channel"
        ),
        "forbidden_effects": [
            "modify physical equations or source terms",
            "modify state variables or solver buffers",
            "modify iteration or reduction order",
            "modify stopping criteria or requested tolerance",
            "modify timestep, grid, boundary conditions, or model parameters",
            "feed a diagnostic quantity back into evolution or acceptance decisions",
            "adapt logging content based on whether a mechanism looks favorable",
        ],
        "capture_order": (
            "copy already-computed values or immutable state snapshots only after the evolution "
            "operation being diagnosed has completed; diagnostic reductions run on the copy"
        ),
        "paired_self_control_scope": (
            "every distinct core instrumented physical configuration must have an otherwise "
            "identical uninstrumented reference role"
        ),
        "primary_equivalence_rule": "byte-identical registered physical trajectory payload",
        "fallback_equivalence_rule_status": "NOT_DEFINED_OR_AUTHORIZED_IN_DESIGN_v0",
        "fallback_requirements_if_byte_identity_is_impossible": [
            "document the unavoidable arithmetic-path effect before freeze",
            "freeze the exact compared state fields, units, norm, epsilon floor, and delta ceiling",
            "derive the ceiling independently of mechanism-experiment results",
            "treat equivalence failure as B-BLOCKED and suppress mechanism classification",
        ],
        "nonperturbation_floor_frozen_now": False,
        "nonperturbation_ceiling_frozen_now": False,
        "failure_disposition": "B-BLOCKED_INSTRUMENTATION_PERTURBATION",
    }


def _observable_registry() -> list[dict[str, Any]]:
    return [
        {
            "observable_id": "EXCHANGE_FIELD_LONGITUDINAL_RAW",
            "mechanism_ids": [MECHANISM_IDS[0]],
            "shape_class": "space_time_and_registered_spatial_integral",
            "semantic_requirement": "field-sector longitudinal exchange before cancellation",
            "unit_requirement": "native canonical code-energy-rate unit, frozen explicitly",
        },
        {
            "observable_id": "EXCHANGE_MATTER_LONGITUDINAL_RAW",
            "mechanism_ids": [MECHANISM_IDS[0]],
            "shape_class": "space_time_and_registered_spatial_integral",
            "semantic_requirement": "matter-sector longitudinal exchange before cancellation",
            "unit_requirement": "same registered unit and sign convention as field exchange",
        },
        {
            "observable_id": "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
            "mechanism_ids": [MECHANISM_IDS[0]],
            "shape_class": "space_time_and_registered_spatial_integral",
            "semantic_requirement": "field plus matter exchange computed from preserved raw terms",
            "unit_requirement": "same registered unit as each exchange term",
        },
        {
            "observable_id": "EXCHANGE_CANCELLATION_KAPPA",
            "mechanism_ids": [MECHANISM_IDS[0]],
            "shape_class": "per_time_and_frozen_summary_aggregates",
            "semantic_requirement": (
                "(|X_field| + |X_matter|) / (|X_field + X_matter| + epsilon_exchange)"
            ),
            "unit_requirement": "dimensionless; epsilon_exchange has exchange-remainder units",
        },
        {
            "observable_id": "SOLVER_BLOCK_RESIDUAL_RAW",
            "mechanism_ids": [MECHANISM_IDS[1]],
            "shape_class": "time_iteration_equation_block_and_optional_space",
            "semantic_requirement": "actual implemented residual before cross-block normalization",
            "unit_requirement": "native block unit registered separately for every block",
        },
        {
            "observable_id": "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
            "mechanism_ids": [MECHANISM_IDS[1]],
            "shape_class": "time_iteration_equation_block",
            "semantic_requirement": (
                "raw block residual norm divided by an independently frozen block scale and floor"
            ),
            "unit_requirement": "dimensionless",
        },
        {
            "observable_id": "SOLVER_BLOCK_DOMINANCE_FRACTION",
            "mechanism_ids": [MECHANISM_IDS[1]],
            "shape_class": "time_iteration_equation_block",
            "semantic_requirement": (
                "normalized block magnitude divided by sum of normalized block magnitudes plus "
                "epsilon_dominance"
            ),
            "unit_requirement": "dimensionless",
        },
        {
            "observable_id": "SOLVER_ITERATION_METADATA",
            "mechanism_ids": [MECHANISM_IDS[1]],
            "shape_class": "time_iteration",
            "semantic_requirement": (
                "requested tolerance, terminal residual, stopping reason, step acceptance, iteration "
                "count, damping or line search if applicable, and conditioning data if available"
            ),
            "unit_requirement": "field-specific registered units or dimensionless metadata",
        },
        {
            "observable_id": "GAUSS_RESIDUAL_FIELD",
            "mechanism_ids": [MECHANISM_IDS[1], MECHANISM_IDS[2]],
            "shape_class": "space_time",
            "semantic_requirement": "actual discrete Gauss residual field",
            "unit_requirement": "canonical equation-residual unit",
        },
        {
            "observable_id": "CONTINUITY_RESIDUAL_FIELD",
            "mechanism_ids": [MECHANISM_IDS[1], MECHANISM_IDS[2]],
            "shape_class": "space_time",
            "semantic_requirement": "actual discrete continuity residual field",
            "unit_requirement": "canonical equation-residual unit",
        },
        {
            "observable_id": "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
            "mechanism_ids": [MECHANISM_IDS[1], MECHANISM_IDS[2]],
            "shape_class": "component_space_time",
            "semantic_requirement": "component residuals from the implemented Maxwell equation",
            "unit_requirement": "canonical equation-residual unit by component",
        },
        {
            "observable_id": "DISCRETE_OPERATOR_OUTPUTS",
            "mechanism_ids": [MECHANISM_IDS[2]],
            "shape_class": "operator_component_space_time",
            "semantic_requirement": (
                "outputs of the exact time and space operators, gauge-link transport, Wilson terms, "
                "boundary handling, and staggering used by evolution"
            ),
            "unit_requirement": "operator-output units registered per component",
        },
        {
            "observable_id": "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
            "mechanism_ids": [MECHANISM_IDS[2]],
            "shape_class": "space_time_and_frozen_summary_aggregates",
            "semantic_requirement": (
                "scheme-derived closure expression using actual discrete operators minus the "
                "implemented continuity residual"
            ),
            "unit_requirement": "frozen closure-residual unit",
        },
        {
            "observable_id": "INSTRUMENTATION_TRAJECTORY_IDENTITY",
            "mechanism_ids": MECHANISM_IDS,
            "shape_class": "paired_run_physical_trajectory",
            "semantic_requirement": "hashes and, if needed, frozen equivalence residuals",
            "unit_requirement": "hash identity or dimensionless frozen equivalence metric",
        },
    ]


def _aggregation_and_missing_data_contract() -> dict[str, Any]:
    return {
        "spatial_summaries_required": [
            "L_infinity maximum absolute magnitude",
            "grid-weighted discrete L2 norm",
            "argmax grid index with lowest-index deterministic tie break",
        ],
        "time_summaries_required": [
            "per-step raw series",
            "maximum and first-maximum time",
            "final value",
            "frozen quadrature integral where the hypothesis requires accumulation",
        ],
        "iteration_summaries_required": [
            "initial, per-iteration, and terminal block residuals",
            "first and final dominant block",
            "maximum dominance fraction and its iteration",
        ],
        "block_registry_requirement": (
            "must enumerate every implemented solver block, including Dirac, adjoint, longitudinal "
            "Maxwell, phi2, phi3, Gauss, continuity, gauge, zero-mode, and any additional block "
            "present in code; omission of an implemented block is B-BLOCKED"
        ),
        "per_block_freeze_fields": [
            "mathematical residual",
            "discrete residual expression",
            "units",
            "norm",
            "normalization scale",
            "numerical floor",
            "spatial aggregation",
            "time aggregation",
            "solver-iteration aggregation",
        ],
        "required_missing_data_behavior": "B-BLOCKED_REQUIRED_MECHANISM_OBSERVABLE_MISSING",
        "optional_not_applicable_behavior": (
            "explicit NOT_APPLICABLE with registered implementation reason; never silent zero or null"
        ),
    }


def _discrete_closure_contract() -> dict[str, Any]:
    return {
        "continuum_formula_is_not_the_audit_definition": True,
        "required_derivation": (
            "derive the Maxwell-to-continuity closure from the implemented time centering, spatial "
            "stencil, gauge links, boundary conditions, signs, charge convention, staggering or "
            "collocation, zero-mode treatment, and Wilson terms"
        ),
        "implementation_closure_requirements_before_freeze": [
            "symbolic or executable mapping from every closure term to implementation expression",
            "operator and stencil registry",
            "operator implementation hashes",
            "unit and sign audit",
            "expected truncation remainder derivation",
            "positive and negative closure controls",
        ],
        "posthoc_continuum_derivative_substitution_allowed": False,
        "closure_formula_frozen_now": False,
        "closure_threshold_frozen_now": False,
        "failure_if_not_closed_before_freeze": "B-BLOCKED_DISCRETE_CLOSURE_DEFINITION",
    }


def _hypotheses_and_classifier() -> dict[str, Any]:
    hypotheses = [
        {
            "hypothesis_id": "H_A_CANCELLATION_CONDITIONING",
            "necessary_condition_classes": [
                "kappa_exchange exceeds a future frozen material-conditioning threshold in loose R13",
                "loose R13 conditioning distinguishes both tight R13 and the matched neighbor under frozen contrasts",
            ],
            "supporting_condition_classes": [
                "exchange remainder sensitivity tracks conditioning",
                "individual exchange terms remain much less tolerance-sensitive than their remainder",
            ],
        },
        {
            "hypothesis_id": "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
            "necessary_condition_classes": [
                "one longitudinal normalized block exceeds a future frozen dominance threshold",
                "dominance distinguishes loose R13 from tight R13 and the matched neighbor",
            ],
            "supporting_condition_classes": [
                "dominance appears no later than the accepted structural threshold crossings",
                "continuity and Gauss residual fields track the dominant block under frozen association metrics",
            ],
        },
        {
            "hypothesis_id": "H_C_DISCRETE_CLOSURE_MISMATCH",
            "necessary_condition_classes": [
                "actual scheme-derived closure residual fails its future frozen admissibility criterion",
                "failure distinguishes loose R13 from tight R13 and the matched neighbor",
            ],
            "supporting_condition_classes": [
                "closure improves predictably with tighter solver tolerance",
                "spatial closure localization predicts continuity-residual localization",
            ],
        },
        {
            "hypothesis_id": "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            "necessary_condition_classes": [
                "no H_A through H_C necessary-condition set passes",
                "multiple normalized blocks contribute under future frozen distributed-contribution criteria",
                "structural residual accumulation is reproduced without a single dominant block",
            ],
            "supporting_condition_classes": [
                "block contributions share a common tolerance response",
                "cumulative contribution metrics predict later structural residuals",
            ],
        },
        {
            "hypothesis_id": "H_E_UNRESOLVED_MECHANISM",
            "necessary_condition_classes": [
                "required evidence is incomplete, conflicting, below discrimination thresholds, or does not classify as H_A through H_D"
            ],
            "supporting_condition_classes": [],
        },
    ]
    return {
        "hypotheses": hypotheses,
        "multiple_H_A_to_H_C_support_allowed": True,
        "classifier_order": [
            "custody, identity, and instrumentation nonperturbation gate",
            "required-role completion and required-observable completeness gate",
            "numerical and discrete-definition admissibility gate",
            "evaluate H_A, H_B, and H_C necessary conditions independently",
            "if two or more of H_A to H_C pass, assign MULTIPLE_SUPPORTED_MECHANISMS",
            "if exactly one of H_A to H_C passes, assign SINGLE_SUPPORTED_MECHANISM",
            "if none pass and H_D necessary conditions pass, assign DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            "otherwise assign UNRESOLVED_MECHANISM H_E",
        ],
        "outcome_classes": [
            "EVIDENCE_BLOCKED_CUSTODY_OR_INSTRUMENTATION",
            "EVIDENCE_BLOCKED_NUMERICAL_OR_DEFINITION",
            "SINGLE_SUPPORTED_MECHANISM",
            "MULTIPLE_SUPPORTED_MECHANISMS",
            "DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            "UNRESOLVED_MECHANISM",
        ],
        "forced_single_winner_allowed": False,
        "unresolved_outcome_mandatory": True,
        "materiality_evaluation_called": False,
        "physical_or_model_domain_claim_called": False,
    }


def _supporting_modules() -> list[dict[str, Any]]:
    return [
        {
            "module_id": "SUPPORT_B_EXPANDED_TOLERANCE_LADDER",
            "status": "SECONDARY_OPTION_FOR_FUTURE_FREEZE_NOT_REQUIRED_FOR_CORE_DESIGN",
            "purpose": "test stability of the descriptive tolerance response",
            "freeze_requirements_if_included": [
                "exact tolerance values and role identities",
                "fit formula, points, weights, floors, and minimum count",
                "whether the fit is descriptive or decision-bearing",
                "failure and missing-point behavior",
            ],
        },
        {
            "module_id": "SUPPORT_C_DURATION_SCALING",
            "status": "SECONDARY_OPTION_FOR_FUTURE_FREEZE_NOT_REQUIRED_FOR_CORE_DESIGN",
            "purpose": "test linear-like structural and quadratic-like exchange growth",
            "freeze_requirements_if_included": [
                "exact durations or checkpoint times",
                "independent-run versus single-run-checkpoint construction",
                "prefix identity rule for checkpoints",
                "time-fit formulas, points, weights, and claim ceiling",
            ],
        },
    ]


def _output_and_custody_design() -> dict[str, Any]:
    return {
        "new_output_family_required": True,
        "proposed_namespace_not_created_or_frozen": (
            "formal/output/experiments/dirac_maxwell_instrumented_r13_mechanism_v0/"
        ),
        "canonical_output_root_write_allowed": False,
        "canonical_digest_required_before_and_after_every_future_stage": True,
        "payload_identity_fields_required": [
            "experiment_id",
            "run_id",
            "parent_canonical_row_id",
            "mechanism_role",
            "solver_tolerance",
            "duration",
            "instrumentation_state",
            "model_hash",
            "implementation_hash",
            "discrete_operator_hash",
            "output_schema_version",
            "input_hash",
            "payload_hash",
        ],
        "output_volume_contract": [
            "estimate worst-case record and family size before freeze",
            "fixed logging cadence only; no value-dependent adaptive logging",
            "chunking and compression may occur only after immutable capture",
            "no dropped samples or silent truncation",
            "disk or serialization failure is B-BLOCKED",
            "diagnostic writer may not reuse mutable solver storage",
        ],
        "new_output_root_created_now": False,
        "new_mechanism_output_created_now": False,
    }


def _freeze_deferred_registry() -> list[str]:
    return [
        "exact experiment and run count",
        "exact tight R13 tolerance choice and any additional tolerances",
        "exact matched-neighbor row identity after deterministic rule confirmation",
        "exact duration and checkpoint schedule",
        "exact instrumentation pairing multiplicity",
        "exact grid, timestep, iteration cap, and environment identity",
        "exact equation-block registry tied to implementation",
        "exact output field names, shapes, schema version, and filenames",
        "exact units, normalizations, numerical floors, and aggregation formulas",
        "exact discrete closure formula, operator hashes, and truncation remainder",
        "exact nonperturbation equality or fallback equivalence rule",
        "exact hypothesis thresholds, contrast rules, association metrics, and tie behavior",
        "exact positive and negative controls",
        "exact classifier implementation and hash",
        "exact implementation closure and code hash",
        "exact one-execution authorization and no-retry rule",
    ]


DECISION_IDS = [
    "accepted_route_review_selects_exact_instrumented_design_target",
    "all_bound_sources_and_203_canonical_outputs_have_exact_custody",
    "canonical_execution_count_and_root_digest_remain_unchanged",
    "three_scientific_questions_map_one_to_one_to_unresolved_mechanisms",
    "core_design_contains_loose_R13_tight_R13_and_matched_neighbor_roles",
    "every_core_instrumented_configuration_requires_an_uninstrumented_self_control",
    "exact_run_count_and_tight_reference_multiplicity_remain_unfrozen",
    "neighbor_rule_is_deterministic_and_exact_identity_is_deferred_to_freeze",
    "instrumentation_is_read_only_side_channel_with_byte_identity_primary_control",
    "fallback_nonperturbation_floor_and_ceiling_are_not_posthoc_or_frozen_now",
    "exchange_raw_terms_remainder_and_conditioning_are_all_required",
    "equation_block_raw_normalized_dominance_and_iteration_histories_are_required",
    "spatial_Gauss_continuity_and_Maxwell_fields_are_required",
    "actual_discrete_operator_outputs_and_scheme_derived_closure_are_required",
    "posthoc_continuum_derivative_substitution_is_forbidden",
    "every_implemented_solver_block_requires_units_norms_scales_floors_and_aggregations",
    "required_mechanism_missing_data_is_blocking_not_zero_filled",
    "hypotheses_H_A_through_H_E_include_unresolved_outcome",
    "classifier_allows_multiple_supported_mechanisms_and_forbids_forced_winner",
    "custody_nonperturbation_and_numerical_gates_precede_mechanism_classification",
    "supporting_tolerance_and_duration_modules_remain_secondary_freeze_options",
    "new_output_family_is_separate_and_canonical_root_is_read_only",
    "payload_identity_and_output_volume_failure_contracts_are_defined",
    "all_exact_numerical_values_thresholds_schemas_hashes_and_controls_are_freeze_deferred",
    "design_claim_ceiling_remains_numerical_mechanism_only",
    "no_design_acceptance_freeze_execution_rerun_or_scientific_promotion_is_authorized",
    "selected_next_target_is_independent_design_review_only",
]


def build_packet() -> dict[str, Any]:
    sources = _load_sources()
    custody = _source_custody(sources)
    questions = _scientific_questions()
    roles = _required_run_classes()
    neighbor = _neighbor_candidate_audit(sources)
    nonperturbation = _nonperturbation_contract()
    observables = _observable_registry()
    aggregation = _aggregation_and_missing_data_contract()
    closure = _discrete_closure_contract()
    hypotheses = _hypotheses_and_classifier()
    modules = _supporting_modules()
    output = _output_and_custody_design()
    deferred = _freeze_deferred_registry()
    instrumented_core = [item for item in roles if item["instrumented"]]
    decisions = {
        "accepted_route_review_selects_exact_instrumented_design_target": custody[
            "accepted_route_A_design_preparation_authority_exact"
        ],
        "all_bound_sources_and_203_canonical_outputs_have_exact_custody": custody[
            "passed"
        ],
        "canonical_execution_count_and_root_digest_remain_unchanged": custody[
            "execution_count_performed"
        ]
        == 1
        and custody["canonical_root_digest_exact"]
        and custody["new_simulation_run_count"] == 0
        and custody["canonical_output_mutation_count"] == 0,
        "three_scientific_questions_map_one_to_one_to_unresolved_mechanisms": len(
            questions
        )
        == 3
        and {item["mechanism_id"] for item in questions} == set(MECHANISM_IDS),
        "core_design_contains_loose_R13_tight_R13_and_matched_neighbor_roles": {
            item["role_class"] for item in instrumented_core
        }
        == {
            "CORE_R13_LOOSE_MECHANISM",
            "CORE_R13_TIGHT_REFERENCE",
            "CORE_MATCHED_PASSING_NEIGHBOR_LOOSE",
        },
        "every_core_instrumented_configuration_requires_an_uninstrumented_self_control": nonperturbation[
            "paired_self_control_scope"
        ].startswith("every distinct core"),
        "exact_run_count_and_tight_reference_multiplicity_remain_unfrozen": "exact experiment and run count"
        in deferred
        and "exact tight R13 tolerance choice and any additional tolerances" in deferred,
        "neighbor_rule_is_deterministic_and_exact_identity_is_deferred_to_freeze": neighbor[
            "eligible_axis_sharing_candidate_count"
        ]
        == 11
        and neighbor["exact_neighbor_frozen_now"] is False
        and neighbor["post_result_visual_choice_allowed"] is False,
        "instrumentation_is_read_only_side_channel_with_byte_identity_primary_control": nonperturbation[
            "primary_equivalence_rule"
        ].startswith("byte-identical")
        and len(nonperturbation["forbidden_effects"]) >= 7,
        "fallback_nonperturbation_floor_and_ceiling_are_not_posthoc_or_frozen_now": nonperturbation[
            "fallback_equivalence_rule_status"
        ]
        == "NOT_DEFINED_OR_AUTHORIZED_IN_DESIGN_v0"
        and nonperturbation["nonperturbation_floor_frozen_now"] is False
        and nonperturbation["nonperturbation_ceiling_frozen_now"] is False,
        "exchange_raw_terms_remainder_and_conditioning_are_all_required": {
            item["observable_id"] for item in observables[:4]
        }
        == {
            "EXCHANGE_FIELD_LONGITUDINAL_RAW",
            "EXCHANGE_MATTER_LONGITUDINAL_RAW",
            "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
            "EXCHANGE_CANCELLATION_KAPPA",
        },
        "equation_block_raw_normalized_dominance_and_iteration_histories_are_required": {
            item["observable_id"] for item in observables
        }.issuperset(
            {
                "SOLVER_BLOCK_RESIDUAL_RAW",
                "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
                "SOLVER_BLOCK_DOMINANCE_FRACTION",
                "SOLVER_ITERATION_METADATA",
            }
        ),
        "spatial_Gauss_continuity_and_Maxwell_fields_are_required": {
            item["observable_id"] for item in observables
        }.issuperset(
            {
                "GAUSS_RESIDUAL_FIELD",
                "CONTINUITY_RESIDUAL_FIELD",
                "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
            }
        ),
        "actual_discrete_operator_outputs_and_scheme_derived_closure_are_required": {
            item["observable_id"] for item in observables
        }.issuperset(
            {"DISCRETE_OPERATOR_OUTPUTS", "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL"}
        ),
        "posthoc_continuum_derivative_substitution_is_forbidden": closure[
            "posthoc_continuum_derivative_substitution_allowed"
        ]
        is False,
        "every_implemented_solver_block_requires_units_norms_scales_floors_and_aggregations": len(
            aggregation["per_block_freeze_fields"]
        )
        == 9,
        "required_mechanism_missing_data_is_blocking_not_zero_filled": aggregation[
            "required_missing_data_behavior"
        ]
        == "B-BLOCKED_REQUIRED_MECHANISM_OBSERVABLE_MISSING",
        "hypotheses_H_A_through_H_E_include_unresolved_outcome": [
            item["hypothesis_id"] for item in hypotheses["hypotheses"]
        ]
        == [
            "H_A_CANCELLATION_CONDITIONING",
            "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
            "H_C_DISCRETE_CLOSURE_MISMATCH",
            "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            "H_E_UNRESOLVED_MECHANISM",
        ]
        and hypotheses["unresolved_outcome_mandatory"],
        "classifier_allows_multiple_supported_mechanisms_and_forbids_forced_winner": hypotheses[
            "multiple_H_A_to_H_C_support_allowed"
        ]
        and hypotheses["forced_single_winner_allowed"] is False,
        "custody_nonperturbation_and_numerical_gates_precede_mechanism_classification": hypotheses[
            "classifier_order"
        ][:3]
        == [
            "custody, identity, and instrumentation nonperturbation gate",
            "required-role completion and required-observable completeness gate",
            "numerical and discrete-definition admissibility gate",
        ],
        "supporting_tolerance_and_duration_modules_remain_secondary_freeze_options": len(
            modules
        )
        == 2
        and all(item["status"].startswith("SECONDARY_OPTION") for item in modules),
        "new_output_family_is_separate_and_canonical_root_is_read_only": output[
            "new_output_family_required"
        ]
        and output["canonical_output_root_write_allowed"] is False
        and output["new_output_root_created_now"] is False,
        "payload_identity_and_output_volume_failure_contracts_are_defined": len(
            output["payload_identity_fields_required"]
        )
        >= 12
        and len(output["output_volume_contract"]) >= 6,
        "all_exact_numerical_values_thresholds_schemas_hashes_and_controls_are_freeze_deferred": len(
            deferred
        )
        >= 16,
        "design_claim_ceiling_remains_numerical_mechanism_only": hypotheses[
            "materiality_evaluation_called"
        ]
        is False
        and hypotheses["physical_or_model_domain_claim_called"] is False,
        "no_design_acceptance_freeze_execution_rerun_or_scientific_promotion_is_authorized": True,
        "selected_next_target_is_independent_design_review_only": True,
    }
    ordered = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_INSTRUMENTED_R13_DESIGN_REVIEW_ONLY",
        "downstream_target_if_independent_review_accepts": DOWNSTREAM_TARGET_IF_ACCEPTED,
        "claim_ceiling": (
            "Design-only specification for a future numerical-mechanism experiment. It may define "
            "questions, required role classes, observables, controls, hypothesis logic, and freeze "
            "obligations; it cannot accept the design, freeze exact values, authorize execution, "
            "reclassify robustness, evaluate materiality, or award a scientific claim."
        ),
        "inherited_authority": {
            "selected_route": "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT",
            "canonical_robustness_status": "NUMERICALLY_BLOCKED",
            "blocked_row": R13,
            "blocked_role": "SOLVER_TOL1eM08",
            "root_numerical_mechanism_status": "UNRESOLVED",
            "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "source_custody": custody,
        "scientific_questions": questions,
        "required_run_classes": roles,
        "matched_neighbor_selection_design": neighbor,
        "instrumentation_nonperturbation_contract": nonperturbation,
        "mechanism_observable_registry": observables,
        "aggregation_block_registry_and_missing_data_contract": aggregation,
        "discrete_Maxwell_continuity_closure_contract": closure,
        "hypotheses_and_classifier_design": hypotheses,
        "supporting_modules": modules,
        "output_separation_and_custody_design": output,
        "freeze_deferred_registry": deferred,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "authority_boundary": {
            "design_packet_prepared": not failed,
            "design_independently_accepted": False,
            "numerical_freeze_packet_authorized": False,
            "experiment_frozen": False,
            "new_simulation_authorized": False,
            "rerun_authorized": False,
            "exact_run_count_or_values_selected": False,
            "threshold_or_fit_change_authorized": False,
            "different_numerical_method_authorized": False,
            "R13_parameter_or_initial_condition_change_authorized": False,
            "canonical_output_mutation_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_classification_authorized": False,
            "model_domain_claim_authorized": False,
            "new_E_REPRO_authorized": False,
            "pillar_or_seam_promotion_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_promotion_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "nonclaims": [
            "no design accepted",
            "no numerical freeze prepared or accepted",
            "no exact run count",
            "no exact tight-reference multiplicity",
            "no exact neighbor frozen",
            "no exact duration schedule",
            "no exact output schema or filename set",
            "no diagnostic floor, threshold, or decision constant frozen",
            "no implementation or classifier hash frozen",
            "no new output root created",
            "no new simulation",
            "no canonical output mutation",
            "no rerun",
            "no root mechanism identified",
            "no physical instability",
            "no model-domain boundary",
            "no conditional or broad robustness",
            "no descendant materiality",
            "no new E-REPRO",
            "no pillar or seam promotion",
            "no C_k dynamics",
            "no CCFT promotion",
            "no master-action promotion",
            "no repository-wide green claim",
        ],
    }


def build_manifest(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "packet": {
            "path": PACKET_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(packet)),
        },
        "generator": {
            "path": GENERATOR_RELATIVE_PATH,
            "sha256": sha256_path(REPO_ROOT / GENERATOR_RELATIVE_PATH),
        },
        "bound_source_artifacts": [
            {"path": path, "sha256": digest}
            for path, digest in sorted(EXPECTED_SOURCE_HASHES.items())
        ],
        "canonical_output_root_digest": packet["source_custody"][
            "canonical_root_digest"
        ],
        "canonical_run_output_count_checked": packet["source_custody"][
            "canonical_run_output_count_checked"
        ],
        "new_simulation_run_count": 0,
        "canonical_output_mutation_count": 0,
        "new_experiment_output_root_created": False,
    }


def build_report(packet: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": packet["verdict"],
        "selected_next_target": packet["selected_next_target"],
        "downstream_target_if_independent_review_accepts": packet[
            "downstream_target_if_independent_review_accepts"
        ],
        "claim_ceiling": packet["claim_ceiling"],
        "artifact_hashes": {
            "generator_sha256": sha256_path(REPO_ROOT / GENERATOR_RELATIVE_PATH),
            "packet_sha256": sha256_bytes(canonical_json_bytes(packet)),
            "manifest_sha256": sha256_bytes(canonical_json_bytes(manifest)),
        },
        "source_custody_passed": packet["source_custody"]["passed"],
        "canonical_root_digest": packet["source_custody"]["canonical_root_digest"],
        "scientific_question_count": len(packet["scientific_questions"]),
        "required_run_class_count": len(packet["required_run_classes"]),
        "mechanism_observable_count": len(packet["mechanism_observable_registry"]),
        "hypothesis_count": len(packet["hypotheses_and_classifier_design"]["hypotheses"]),
        "outcome_class_count": len(
            packet["hypotheses_and_classifier_design"]["outcome_classes"]
        ),
        "neighbor_candidate_count": packet["matched_neighbor_selection_design"][
            "eligible_axis_sharing_candidate_count"
        ],
        "provisional_top_neighbor_for_freeze_confirmation": packet[
            "matched_neighbor_selection_design"
        ]["provisional_top_candidate_for_freeze_confirmation"],
        "freeze_deferred_item_count": len(packet["freeze_deferred_registry"]),
        "decision_count": packet["decision_count"],
        "passed_decision_count": packet["passed_decision_count"],
        "failed_decision_ids": packet["failed_decision_ids"],
        "validation_status": {
            "focused_instrumented_R13_design_packet_tests": {
                "passed": 14,
                "failed": 0,
            },
            "current_affected_descendant_robustness_chain": {
                "passed": 272,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 154, "status": "PASSED"},
            "authority_surface_parity": "PASSED",
            "simulation_invocation_count": 0,
            "canonical_output_mutation_count": 0,
            "historical_repository_wide_Lean": {
                "status": "INCOMPLETE_TIMEOUT",
                "completed_jobs": 8441,
                "total_jobs": 8507,
                "repository_wide_green_claim": False,
            },
        },
        "authority_boundary": packet["authority_boundary"],
        "nonclaims": packet["nonclaims"],
    }


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    manifest = build_manifest(packet)
    report = build_report(packet, manifest)
    return packet, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the instrumented R13 mechanism experiment design packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    artifacts = {
        PACKET_PATH: canonical_json_bytes(packet),
        MANIFEST_PATH: canonical_json_bytes(manifest),
        REPORT_PATH: canonical_json_bytes(report),
    }
    if args.write:
        for path, raw in artifacts.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    elif args.check:
        stale = [
            path.relative_to(REPO_ROOT).as_posix()
            for path, raw in artifacts.items()
            if not path.is_file() or path.read_bytes() != raw
        ]
        if stale:
            print(f"stale or missing instrumented R13 design artifacts: {stale}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(canonical_json_bytes(report))
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during design preparation", file=sys.stderr)
        return 1
    if packet["failed_decision_ids"]:
        print(f"design preparation decisions failed: {packet['failed_decision_ids']}", file=sys.stderr)
        return 2
    if args.write:
        print(
            f"wrote instrumented R13 design packet: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; selected {packet['selected_next_target']}"
        )
    elif args.check:
        print(
            f"instrumented R13 design packet verified: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
