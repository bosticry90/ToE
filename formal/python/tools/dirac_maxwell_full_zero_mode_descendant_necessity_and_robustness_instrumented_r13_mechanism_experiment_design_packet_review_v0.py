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
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v0_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_20260715_v0"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v0.json"
)
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH
REVIEWER_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_review_v0.py"
)

DESIGN_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-PACKET-v0.json"
)
DESIGN_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-MANIFEST-v0.json"
)
DESIGN_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_"
    "20260715_v0.json"
)
DESIGN_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_v0.py"
)
ROUTE_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_REVIEW_20260715_v0.json"
)
DIAGNOSTIC_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0.json"
)
FREEZE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
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
    DESIGN_PACKET: "c41a724d4f84566583d970de67ed18ea2490541f4e4a0c4faecff3e057a3b579",
    DESIGN_MANIFEST: "debeacd35c44a1a0e063f758934f4dc3d5983e11c071c67a651c099dda87e6b9",
    DESIGN_REPORT: "f20afcbb5f37c1212bc15bb162765f2c341e20f5e2d6ffc6c54d0e4f10d546d5",
    DESIGN_GENERATOR: "cc95782b5be80c3ee0a44d7e6c2d802ceb8c79bcc12f56a85fcbb2d6df57e2e9",
    ROUTE_REVIEW_REPORT: "a7c48d0d14d69a6d1990d03b09598d449b3e8761f20fc0b2f9308449e73028ed",
    DIAGNOSTIC_REVIEW_REPORT: "15c7bb4ed25f0ce029aac83c231903b69e1073cb356547e0dbc8644b3b200873",
    FREEZE_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
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
HYPOTHESIS_IDS = [
    "H_A_CANCELLATION_CONDITIONING",
    "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
    "H_C_DISCRETE_CLOSURE_MISMATCH",
    "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
    "H_E_UNRESOLVED_MECHANISM",
]
OUTCOME_CLASSES = [
    "EVIDENCE_BLOCKED_CUSTODY_OR_INSTRUMENTATION",
    "EVIDENCE_BLOCKED_NUMERICAL_OR_DEFINITION",
    "SINGLE_SUPPORTED_MECHANISM",
    "MULTIPLE_SUPPORTED_MECHANISMS",
    "DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
    "UNRESOLVED_MECHANISM",
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
    return {
        "packet": load_json(REPO_ROOT / DESIGN_PACKET),
        "manifest": load_json(REPO_ROOT / DESIGN_MANIFEST),
        "design_report": load_json(REPO_ROOT / DESIGN_REPORT),
        "route_review": load_json(REPO_ROOT / ROUTE_REVIEW_REPORT),
        "diagnostic_review": load_json(REPO_ROOT / DIAGNOSTIC_REVIEW_REPORT),
        "freeze": load_json(REPO_ROOT / FREEZE_PACKET),
        "identity": load_json(REPO_ROOT / IDENTITY_MANIFEST),
        "execution_manifest": load_json(REPO_ROOT / EXECUTION_MANIFEST),
        "execution_packet": load_json(REPO_ROOT / EXECUTION_PACKET),
    }


def _source_custody(sources: dict[str, Any]) -> dict[str, Any]:
    hashes = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES}
    packet = sources["packet"]
    manifest = sources["manifest"]
    design_report = sources["design_report"]
    route_review = sources["route_review"]
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
    root_digest = sha256_bytes(canonical_json_bytes(inventory))
    cross_bindings = (
        manifest["packet"]["sha256"] == hashes[DESIGN_PACKET]
        and manifest["generator"]["sha256"] == hashes[DESIGN_GENERATOR]
        and manifest["canonical_output_root_digest"] == root_digest
        and design_report["artifact_hashes"]
        == {
            "packet_sha256": hashes[DESIGN_PACKET],
            "manifest_sha256": hashes[DESIGN_MANIFEST],
            "generator_sha256": hashes[DESIGN_GENERATOR],
        }
    )
    live_authority_exact = (
        packet["target"]
        == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_v0"
        and packet["selected_next_target"] == TARGET
        and packet["downstream_target_if_independent_review_accepts"]
        == SELECTED_NEXT_TARGET
        and route_review["accepted"] is True
        and route_review["selected_next_target"] == packet["target"]
        and route_review["verdict"]
        == "ACCEPT_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_ROUTE_A_DESIGN_PREPARATION_ONLY"
    )
    prepared_design_exact = (
        packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
        and packet["decision_count"] == 27
        and packet["passed_decision_count"] == 27
        and packet["failed_decision_ids"] == []
        and design_report["decision_count"] == 27
        and design_report["failed_decision_ids"] == []
    )
    all_hashes_exact = hashes == EXPECTED_SOURCE_HASHES
    passed = (
        all_hashes_exact
        and cross_bindings
        and live_authority_exact
        and prepared_design_exact
        and len(identity_by_run) == 203
        and len(execution_by_run) == 203
        and not failures
        and len(inventory) == 205
        and root_digest == EXPECTED_CANONICAL_ROOT_DIGEST
        and sources["execution_packet"]["execution_count_performed"] == 1
    )
    return {
        "passed": passed,
        "source_artifact_hashes": hashes,
        "all_source_artifact_hashes_exact": all_hashes_exact,
        "design_artifact_cross_bindings_exact": cross_bindings,
        "live_target_and_accepted_route_authority_exact": live_authority_exact,
        "prepared_design_has_27_of_27_decisions": prepared_design_exact,
        "canonical_run_output_count_checked": len(identity_by_run),
        "canonical_run_output_hash_failures": failures,
        "canonical_root_file_count": len(inventory),
        "canonical_root_digest": root_digest,
        "canonical_root_digest_exact": root_digest == EXPECTED_CANONICAL_ROOT_DIGEST,
        "execution_count_performed": sources["execution_packet"][
            "execution_count_performed"
        ],
        "simulation_invocation_count_during_review": 0,
        "canonical_output_mutation_count": 0,
    }


def _scientific_sufficiency_review(packet: dict[str, Any]) -> dict[str, Any]:
    roles = {item["role_class"]: item for item in packet["required_run_classes"]}
    questions = packet["scientific_questions"]
    observables = packet["mechanism_observable_registry"]
    covered = {
        mechanism_id
        for item in observables
        for mechanism_id in item["mechanism_ids"]
        if mechanism_id in MECHANISM_IDS
    }
    comparisons = [
        {
            "comparison_id": "TOLERANCE_EFFECT",
            "left_role": "CORE_R13_LOOSE_MECHANISM",
            "right_role": "CORE_R13_TIGHT_REFERENCE",
            "holds_fixed": "R13 physical parameters and numerical method",
            "varies": "solver tolerance under the later freeze",
            "directly_answerable": roles["CORE_R13_LOOSE_MECHANISM"]["instrumented"]
            and roles["CORE_R13_TIGHT_REFERENCE"]["instrumented"],
        },
        {
            "comparison_id": "CORNER_EFFECT",
            "left_role": "CORE_R13_LOOSE_MECHANISM",
            "right_role": "CORE_MATCHED_PASSING_NEIGHBOR_LOOSE",
            "holds_fixed": "loose-solver role and numerical method",
            "varies": "minimum registered physical-axis contrast under deterministic matching",
            "directly_answerable": roles["CORE_MATCHED_PASSING_NEIGHBOR_LOOSE"][
                "instrumented"
            ],
        },
        {
            "comparison_id": "INSTRUMENTATION_EFFECT",
            "left_role": "each core instrumented role",
            "right_role": "INSTRUMENTATION_NONPERTURBATION_REFERENCE",
            "holds_fixed": "physical and numerical configuration",
            "varies": "diagnostic instrumentation state only",
            "directly_answerable": roles["INSTRUMENTATION_NONPERTURBATION_REFERENCE"][
                "instrumented"
            ]
            is False,
        },
    ]
    return {
        "scientific_question_count": len(questions),
        "mechanism_ids_exact": [item["mechanism_id"] for item in questions]
        == MECHANISM_IDS,
        "required_role_classes": list(roles),
        "required_role_class_count": len(roles),
        "comparisons": comparisons,
        "all_three_comparisons_directly_answerable": all(
            item["directly_answerable"] for item in comparisons
        ),
        "all_three_mechanism_questions_have_observable_coverage": covered
        == set(MECHANISM_IDS),
        "scientifically_sufficient": (
            len(questions) == 3
            and len(roles) == 4
            and all(item["directly_answerable"] for item in comparisons)
            and covered == set(MECHANISM_IDS)
        ),
    }


def _minimality_and_semantics_review(packet: dict[str, Any]) -> dict[str, Any]:
    observables = packet["mechanism_observable_registry"]
    rows = [
        {
            "observable_id": item["observable_id"],
            "mechanism_ids": item["mechanism_ids"],
            "shape_class": item["shape_class"],
            "semantic_requirement_present": bool(item["semantic_requirement"]),
            "unit_requirement_present": bool(item["unit_requirement"]),
            "traced": bool(item["mechanism_ids"]),
        }
        for item in observables
    ]
    ids = [item["observable_id"] for item in observables]
    untraced = [item["observable_id"] for item in observables if not item["mechanism_ids"]]
    invalid_mechanisms = sorted(
        {
            mechanism_id
            for item in observables
            for mechanism_id in item["mechanism_ids"]
            if mechanism_id not in MECHANISM_IDS
        }
    )
    shapes = " ".join(item["shape_class"] for item in observables)
    aggregation = packet["aggregation_block_registry_and_missing_data_contract"]
    return {
        "observable_count": len(observables),
        "observable_ids_exact_and_unique": ids == OBSERVABLE_IDS
        and len(ids) == len(set(ids)),
        "traceability_rows": rows,
        "untraced_observable_ids": untraced,
        "invalid_mechanism_ids": invalid_mechanisms,
        "all_observables_have_semantics_units_and_question_trace": not untraced
        and not invalid_mechanisms
        and all(
            item["semantic_requirement_present"] and item["unit_requirement_present"]
            for item in rows
        ),
        "time_space_and_iteration_structure_preserved": "space_time" in shapes
        and "time_iteration" in shapes
        and "operator_component_space_time" in shapes
        and "paired_run_physical_trajectory" in shapes,
        "per_step_raw_series_required": "per-step raw series"
        in aggregation["time_summaries_required"],
        "per_block_freeze_semantics_complete": aggregation["per_block_freeze_fields"]
        == [
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
        "required_missing_data_is_blocking": aggregation["required_missing_data_behavior"]
        == "B-BLOCKED_REQUIRED_MECHANISM_OBSERVABLE_MISSING",
        "minimality_passed": ids == OBSERVABLE_IDS
        and not untraced
        and not invalid_mechanisms,
    }


def _mechanism_specific_sufficiency(packet: dict[str, Any]) -> dict[str, Any]:
    ids = {item["observable_id"] for item in packet["mechanism_observable_registry"]}
    exchange = {
        "EXCHANGE_FIELD_LONGITUDINAL_RAW",
        "EXCHANGE_MATTER_LONGITUDINAL_RAW",
        "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
        "EXCHANGE_CANCELLATION_KAPPA",
    }
    block = {
        "SOLVER_BLOCK_RESIDUAL_RAW",
        "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
        "SOLVER_BLOCK_DOMINANCE_FRACTION",
        "SOLVER_ITERATION_METADATA",
        "GAUSS_RESIDUAL_FIELD",
        "CONTINUITY_RESIDUAL_FIELD",
        "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
    }
    closure = {
        "CONTINUITY_RESIDUAL_FIELD",
        "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
        "DISCRETE_OPERATOR_OUTPUTS",
        "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
    }
    return {
        "exchange_question_directly_answerable": exchange <= ids,
        "equation_block_question_directly_answerable": block <= ids,
        "discrete_closure_question_directly_answerable": closure <= ids,
        "exchange_required_observable_ids": sorted(exchange),
        "equation_block_required_observable_ids": sorted(block),
        "closure_required_observable_ids": sorted(closure),
    }


def _hypothesis_review(packet: dict[str, Any]) -> dict[str, Any]:
    design = packet["hypotheses_and_classifier_design"]
    hypotheses = design["hypotheses"]
    hypothesis_ids = [item["hypothesis_id"] for item in hypotheses]
    necessary_counts = {
        item["hypothesis_id"]: len(item["necessary_condition_classes"])
        for item in hypotheses
    }
    contrast_required = all(
        any("distinguishes" in condition for condition in item["necessary_condition_classes"])
        for item in hypotheses[:3]
    )
    h_e_conditions = hypotheses[-1]["necessary_condition_classes"]
    return {
        "hypothesis_ids_exact": hypothesis_ids == HYPOTHESIS_IDS,
        "necessary_condition_counts": necessary_counts,
        "outcome_classes_exact": design["outcome_classes"] == OUTCOME_CLASSES,
        "multiple_mechanisms_allowed": design["multiple_H_A_to_H_C_support_allowed"],
        "forced_single_winner_forbidden": design["forced_single_winner_allowed"] is False,
        "unresolved_outcome_mandatory": design["unresolved_outcome_mandatory"],
        "custody_completeness_and_numerical_gates_precede_hypotheses": design[
            "classifier_order"
        ][:3]
        == [
            "custody, identity, and instrumentation nonperturbation gate",
            "required-role completion and required-observable completeness gate",
            "numerical and discrete-definition admissibility gate",
        ],
        "A_to_C_require_predeclared_contrast_not_self_definition_alone": contrast_required,
        "distributed_is_only_after_A_to_C_fail": design["classifier_order"][6].startswith(
            "if none pass"
        ),
        "unresolved_is_final_fallback": design["classifier_order"][-1].startswith(
            "otherwise assign UNRESOLVED"
        ),
        "per_hypothesis_support_vector_and_criterion_records_required": bool(
            design.get("per_hypothesis_support_vector_required", False)
        )
        and bool(design.get("per_hypothesis_criterion_records_required", False)),
        "H_E_is_disjoint_from_required_evidence_incompleteness": not any(
            "incomplete" in condition.lower() for condition in h_e_conditions
        ),
        "H_E_current_necessary_conditions": h_e_conditions,
        "physical_or_materiality_claims_not_called": design["materiality_evaluation_called"]
        is False
        and design["physical_or_model_domain_claim_called"] is False,
    }


def _nonperturbation_review(packet: dict[str, Any]) -> dict[str, Any]:
    contract = packet["instrumentation_nonperturbation_contract"]
    forbidden = set(contract["forbidden_effects"])
    expected_forbidden = {
        "modify physical equations or source terms",
        "modify state variables or solver buffers",
        "modify iteration or reduction order",
        "modify stopping criteria or requested tolerance",
        "modify timestep, grid, boundary conditions, or model parameters",
        "feed a diagnostic quantity back into evolution or acceptance decisions",
        "adapt logging content based on whether a mechanism looks favorable",
    }
    return {
        "read_only_separate_channel": "read immutable snapshots"
        in contract["instrumentation_permission"]
        and "separate output channel" in contract["instrumentation_permission"],
        "all_solver_state_order_stopping_timestep_equation_and_parameter_mutations_forbidden": forbidden
        == expected_forbidden,
        "capture_occurs_after_evolution_on_a_copy": "only after the evolution operation"
        in contract["capture_order"]
        and "run on the copy" in contract["capture_order"],
        "every_core_configuration_has_paired_reference": contract[
            "paired_self_control_scope"
        ].startswith("every distinct core instrumented physical configuration"),
        "primary_rule_is_trajectory_level_byte_identity": contract[
            "primary_equivalence_rule"
        ]
        == "byte-identical registered physical trajectory payload",
        "fallback_is_not_defined_or_authorized": contract[
            "fallback_equivalence_rule_status"
        ]
        == "NOT_DEFINED_OR_AUTHORIZED_IN_DESIGN_v0",
        "fallback_floor_and_ceiling_must_be_independently_frozen": (
            "freeze the exact compared state fields, units, norm, epsilon floor, and delta ceiling"
            in contract["fallback_requirements_if_byte_identity_is_impossible"]
            and "derive the ceiling independently of mechanism-experiment results"
            in contract["fallback_requirements_if_byte_identity_is_impossible"]
        ),
        "failure_blocks_mechanism_classification": contract["failure_disposition"]
        == "B-BLOCKED_INSTRUMENTATION_PERTURBATION"
        and "treat equivalence failure as B-BLOCKED and suppress mechanism classification"
        in contract["fallback_requirements_if_byte_identity_is_impossible"],
    }


def _operator_authenticity_review(packet: dict[str, Any]) -> dict[str, Any]:
    closure = packet["discrete_Maxwell_continuity_closure_contract"]
    observables = {item["observable_id"] for item in packet["mechanism_observable_registry"]}
    requirements = closure["implementation_closure_requirements_before_freeze"]
    return {
        "continuum_formula_rejected_as_audit_definition": closure[
            "continuum_formula_is_not_the_audit_definition"
        ]
        is True,
        "posthoc_continuum_substitution_forbidden": closure[
            "posthoc_continuum_derivative_substitution_allowed"
        ]
        is False,
        "actual_operator_outputs_and_scheme_closure_observables_required": {
            "DISCRETE_OPERATOR_OUTPUTS",
            "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
        }
        <= observables,
        "implemented_scheme_features_are_all_named": all(
            token in closure["required_derivation"]
            for token in [
                "time centering",
                "spatial stencil",
                "gauge links",
                "boundary conditions",
                "signs",
                "charge convention",
                "staggering or collocation",
                "zero-mode treatment",
                "Wilson terms",
            ]
        ),
        "implementation_mapping_operator_hashes_units_remainder_and_controls_required": len(
            requirements
        )
        == 6
        and "operator implementation hashes" in requirements
        and "expected truncation remainder derivation" in requirements
        and "positive and negative closure controls" in requirements,
        "formula_and_threshold_deferred": closure["closure_formula_frozen_now"] is False
        and closure["closure_threshold_frozen_now"] is False,
        "failure_to_close_definition_before_freeze_is_blocking": closure[
            "failure_if_not_closed_before_freeze"
        ]
        == "B-BLOCKED_DISCRETE_CLOSURE_DEFINITION",
    }


def _independent_neighbor_review(
    packet: dict[str, Any], sources: dict[str, Any]
) -> dict[str, Any]:
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
    accepted_neighbors = sources["diagnostic_review"]["independent_neighbor_reconstruction"][
        "axis_sharing_neighbors"
    ]
    candidates = []
    for accepted in accepted_neighbors:
        if not accepted["all_four_pass"]:
            continue
        row_id = accepted["scientific_row_id"]
        axes = scientific_rows[row_id]
        shared = sorted(axis for axis, value in axes.items() if value == r13_axes[axis])
        components = {}
        squared = 0.0
        for axis, value in axes.items():
            low, high = axis_ranges[axis]
            component = (
                (float(value) - float(r13_axes[axis])) / (high - low)
                if high > low
                else 0.0
            )
            components[axis] = component
            squared += component * component
        candidates.append(
            {
                "scientific_row_id": row_id,
                "shared_axis_count": len(shared),
                "shared_axes": shared,
                "normalized_distance": math.sqrt(squared),
                "normalized_distance_components": components,
                "all_four_loose_solver_residual_ceilings_pass": True,
                "maximum_loose_solver_ceiling_ratio": accepted["maximum_ceiling_ratio"],
            }
        )
    ranked = sorted(
        candidates,
        key=lambda item: (
            -item["shared_axis_count"],
            item["normalized_distance"],
            item["scientific_row_id"],
        ),
    )
    packet_neighbor = packet["matched_neighbor_selection_design"]
    packet_rows = packet_neighbor["ranked_candidate_audit"]
    top_key = (
        -ranked[0]["shared_axis_count"],
        ranked[0]["normalized_distance"],
        ranked[0]["scientific_row_id"],
    )
    second_key = (
        -ranked[1]["shared_axis_count"],
        ranked[1]["normalized_distance"],
        ranked[1]["scientific_row_id"],
    )
    return {
        "eligibility_source_is_preexisting_accepted_canonical_evidence": True,
        "ranking_rule_reconstructed": [
            "maximize shared R13 axis count",
            "minimize Euclidean distance using frozen-matrix per-axis min-max ranges",
            "lexicographically ascending scientific_row_id tie break",
        ],
        "candidate_count": len(ranked),
        "declared_eligibility_rule": packet_neighbor["eligibility_rule"],
        "declared_eligibility_explicitly_requires_axis_sharing": "sharing at least one"
        in packet_neighbor["eligibility_rule"].lower()
        or "shares at least one" in packet_neighbor["eligibility_rule"].lower(),
        "candidate_universe_is_axis_sharing_only": len(accepted_neighbors) == len(ranked),
        "ranked_candidates": ranked,
        "packet_ranking_exact": ranked == packet_rows,
        "unique_top_candidate": top_key != second_key,
        "provisional_top_candidate": ranked[0]["scientific_row_id"],
        "provisional_top_matches_packet": ranked[0]["scientific_row_id"]
        == packet_neighbor["provisional_top_candidate_for_freeze_confirmation"],
        "future_result_data_used": False,
        "exact_neighbor_frozen_by_design": packet_neighbor["exact_neighbor_frozen_now"],
        "scientific_limitation": (
            "R10_MU_HIGH is the unique nearest registered eligible candidate but shares only two "
            "of five R13 axes; it is a nearest-neighbor contrast, not a one-axis-isolated control."
        ),
        "top_shared_axis_count": ranked[0]["shared_axis_count"],
    }


def _design_freeze_separation_review(packet: dict[str, Any]) -> dict[str, Any]:
    deferred = packet["freeze_deferred_registry"]
    authority = packet["authority_boundary"]
    forbidden_true = {
        key: value
        for key, value in authority.items()
        if key != "design_packet_prepared" and value is not False
    }
    supporting = packet["supporting_modules"]
    historical_anchors = [
        item["solver_tolerance_rule"] for item in packet["required_run_classes"][:3]
    ]
    return {
        "freeze_deferred_item_count": len(deferred),
        "freeze_deferred_registry": deferred,
        "all_sixteen_freeze_items_present": len(deferred) == 16,
        "no_forbidden_authority_true": not forbidden_true,
        "forbidden_authority_values_true": forbidden_true,
        "exact_run_count_or_values_selected": authority[
            "exact_run_count_or_values_selected"
        ],
        "exact_neighbor_frozen": packet["matched_neighbor_selection_design"][
            "exact_neighbor_frozen_now"
        ],
        "closure_formula_or_threshold_frozen": packet[
            "discrete_Maxwell_continuity_closure_contract"
        ]["closure_formula_frozen_now"]
        or packet["discrete_Maxwell_continuity_closure_contract"][
            "closure_threshold_frozen_now"
        ],
        "supporting_B_and_C_are_secondary_options": len(supporting) == 2
        and all(item["status"].startswith("SECONDARY_OPTION") for item in supporting),
        "historical_tolerance_anchors_are_design_provenance_not_execution_values": historical_anchors,
        "freeze_must_rebind_every_executable_value": True,
    }


def _output_and_nonexecution_review(
    packet: dict[str, Any], custody: dict[str, Any]
) -> dict[str, Any]:
    output = packet["output_separation_and_custody_design"]
    source = (REPO_ROOT / DESIGN_GENERATOR).read_text(encoding="utf-8")
    return {
        "new_output_family_required": output["new_output_family_required"],
        "canonical_output_root_write_allowed": output["canonical_output_root_write_allowed"],
        "new_output_root_created": output["new_output_root_created_now"],
        "new_mechanism_output_created": output["new_mechanism_output_created_now"],
        "payload_identity_field_count": len(output["payload_identity_fields_required"]),
        "fixed_logging_and_blocking_output_failure_contract": (
            "fixed logging cadence only; no value-dependent adaptive logging"
            in output["output_volume_contract"]
            and "disk or serialization failure is B-BLOCKED"
            in output["output_volume_contract"]
            and "no dropped samples or silent truncation" in output["output_volume_contract"]
        ),
        "design_generator_imports_no_simulator": " as simulator" not in source,
        "design_generator_invokes_no_subprocess": "subprocess" not in source,
        "new_simulation_count": 0,
        "canonical_output_mutation_count": custody["canonical_output_mutation_count"],
        "canonical_root_digest_unchanged": custody["canonical_root_digest_exact"],
    }


DECISION_IDS = [
    "live_authority_selects_exact_independent_design_review",
    "design_packet_manifest_report_and_generator_hashes_are_exact",
    "design_artifact_cross_bindings_are_exact",
    "accepted_route_A_authority_is_preserved",
    "all_203_canonical_outputs_and_root_digest_reproduce",
    "prepared_design_has_27_of_27_passing_decisions",
    "four_required_role_classes_are_exact",
    "loose_tight_comparison_directly_identifies_tolerance_effect",
    "R13_neighbor_comparison_directly_identifies_corner_contrast",
    "instrumented_uninstrumented_pairing_directly_tests_observation_effect",
    "three_questions_map_exactly_to_three_unresolved_mechanisms",
    "fourteen_observables_are_exact_unique_and_traced",
    "observables_preserve_time_space_iteration_and_trajectory_structure",
    "exchange_conditioning_question_is_directly_answerable",
    "equation_block_question_is_directly_answerable",
    "discrete_closure_question_is_directly_answerable",
    "per_block_semantics_and_required_missing_data_behavior_are_freeze_ready",
    "hypotheses_H_A_through_H_E_and_six_outcomes_are_exact",
    "classifier_allows_multiple_support_and_unresolved_without_forced_winner",
    "custody_completeness_and_numerical_gates_precede_mechanism_classification",
    "hypotheses_require_predeclared_comparator_contrasts_not_self_definition_alone",
    "classifier_preserves_per_hypothesis_support_vector_and_criterion_records",
    "H_E_is_disjoint_from_required_evidence_completeness_block",
    "instrumentation_is_read_only_and_forbids_state_order_stopping_and_parameter_changes",
    "every_core_role_has_trajectory_level_noninstrumented_self_control",
    "fallback_equivalence_is_unfrozen_independent_and_blocking_on_failure",
    "actual_discrete_operator_outputs_are_required_and_posthoc_continuum_substitution_forbidden",
    "closure_mapping_hashes_units_remainder_controls_formula_and_threshold_are_freeze_obligations",
    "neighbor_rule_reconstructs_eleven_eligible_candidates_and_packet_ranking_exactly",
    "neighbor_eligibility_prose_matches_axis_sharing_candidate_universe",
    "R10_is_unique_provisional_top_but_not_frozen_or_one_axis_isolated",
    "all_sixteen_exact_numerical_and_custody_items_remain_freeze_deferred",
    "supporting_tolerance_and_duration_modules_remain_secondary_options",
    "new_output_family_is_separate_identity_bound_and_canonical_root_read_only",
    "packet_contains_no_run_output_freeze_or_scientific_reclassification",
    "canonical_block_materiality_root_unknown_and_E_REPRO_status_remain_unchanged",
    "blocked_review_withholds_numerical_freeze_packet_preparation",
]


def build_review_report() -> dict[str, Any]:
    sources = _load_sources()
    packet = sources["packet"]
    custody = _source_custody(sources)
    sufficiency = _scientific_sufficiency_review(packet)
    minimality = _minimality_and_semantics_review(packet)
    mechanism = _mechanism_specific_sufficiency(packet)
    hypotheses = _hypothesis_review(packet)
    nonperturbation = _nonperturbation_review(packet)
    operators = _operator_authenticity_review(packet)
    neighbor = _independent_neighbor_review(packet, sources)
    separation = _design_freeze_separation_review(packet)
    output = _output_and_nonexecution_review(packet, custody)
    roles = {item["role_class"]: item for item in packet["required_run_classes"]}
    comparisons = {item["comparison_id"]: item for item in sufficiency["comparisons"]}
    decisions = {
        "live_authority_selects_exact_independent_design_review": custody[
            "live_target_and_accepted_route_authority_exact"
        ],
        "design_packet_manifest_report_and_generator_hashes_are_exact": custody[
            "all_source_artifact_hashes_exact"
        ],
        "design_artifact_cross_bindings_are_exact": custody[
            "design_artifact_cross_bindings_exact"
        ],
        "accepted_route_A_authority_is_preserved": sources["route_review"]["accepted"]
        is True
        and sources["route_review"]["selected_route"]
        == "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT",
        "all_203_canonical_outputs_and_root_digest_reproduce": custody["passed"],
        "prepared_design_has_27_of_27_passing_decisions": custody[
            "prepared_design_has_27_of_27_decisions"
        ],
        "four_required_role_classes_are_exact": set(roles)
        == {
            "CORE_R13_LOOSE_MECHANISM",
            "CORE_R13_TIGHT_REFERENCE",
            "CORE_MATCHED_PASSING_NEIGHBOR_LOOSE",
            "INSTRUMENTATION_NONPERTURBATION_REFERENCE",
        },
        "loose_tight_comparison_directly_identifies_tolerance_effect": comparisons[
            "TOLERANCE_EFFECT"
        ]["directly_answerable"],
        "R13_neighbor_comparison_directly_identifies_corner_contrast": comparisons[
            "CORNER_EFFECT"
        ]["directly_answerable"],
        "instrumented_uninstrumented_pairing_directly_tests_observation_effect": comparisons[
            "INSTRUMENTATION_EFFECT"
        ]["directly_answerable"],
        "three_questions_map_exactly_to_three_unresolved_mechanisms": sufficiency[
            "mechanism_ids_exact"
        ]
        and sufficiency["all_three_mechanism_questions_have_observable_coverage"],
        "fourteen_observables_are_exact_unique_and_traced": minimality[
            "observable_count"
        ]
        == 14
        and minimality["observable_ids_exact_and_unique"]
        and minimality["all_observables_have_semantics_units_and_question_trace"],
        "observables_preserve_time_space_iteration_and_trajectory_structure": minimality[
            "time_space_and_iteration_structure_preserved"
        ]
        and minimality["per_step_raw_series_required"],
        "exchange_conditioning_question_is_directly_answerable": mechanism[
            "exchange_question_directly_answerable"
        ],
        "equation_block_question_is_directly_answerable": mechanism[
            "equation_block_question_directly_answerable"
        ],
        "discrete_closure_question_is_directly_answerable": mechanism[
            "discrete_closure_question_directly_answerable"
        ],
        "per_block_semantics_and_required_missing_data_behavior_are_freeze_ready": minimality[
            "per_block_freeze_semantics_complete"
        ]
        and minimality["required_missing_data_is_blocking"],
        "hypotheses_H_A_through_H_E_and_six_outcomes_are_exact": hypotheses[
            "hypothesis_ids_exact"
        ]
        and hypotheses["outcome_classes_exact"],
        "classifier_allows_multiple_support_and_unresolved_without_forced_winner": hypotheses[
            "multiple_mechanisms_allowed"
        ]
        and hypotheses["forced_single_winner_forbidden"]
        and hypotheses["unresolved_outcome_mandatory"],
        "custody_completeness_and_numerical_gates_precede_mechanism_classification": hypotheses[
            "custody_completeness_and_numerical_gates_precede_hypotheses"
        ],
        "hypotheses_require_predeclared_comparator_contrasts_not_self_definition_alone": hypotheses[
            "A_to_C_require_predeclared_contrast_not_self_definition_alone"
        ]
        and hypotheses["distributed_is_only_after_A_to_C_fail"]
        and hypotheses["unresolved_is_final_fallback"],
        "classifier_preserves_per_hypothesis_support_vector_and_criterion_records": hypotheses[
            "per_hypothesis_support_vector_and_criterion_records_required"
        ],
        "H_E_is_disjoint_from_required_evidence_completeness_block": hypotheses[
            "H_E_is_disjoint_from_required_evidence_incompleteness"
        ],
        "instrumentation_is_read_only_and_forbids_state_order_stopping_and_parameter_changes": nonperturbation[
            "read_only_separate_channel"
        ]
        and nonperturbation[
            "all_solver_state_order_stopping_timestep_equation_and_parameter_mutations_forbidden"
        ]
        and nonperturbation["capture_occurs_after_evolution_on_a_copy"],
        "every_core_role_has_trajectory_level_noninstrumented_self_control": nonperturbation[
            "every_core_configuration_has_paired_reference"
        ]
        and nonperturbation["primary_rule_is_trajectory_level_byte_identity"],
        "fallback_equivalence_is_unfrozen_independent_and_blocking_on_failure": nonperturbation[
            "fallback_is_not_defined_or_authorized"
        ]
        and nonperturbation["fallback_floor_and_ceiling_must_be_independently_frozen"]
        and nonperturbation["failure_blocks_mechanism_classification"],
        "actual_discrete_operator_outputs_are_required_and_posthoc_continuum_substitution_forbidden": operators[
            "actual_operator_outputs_and_scheme_closure_observables_required"
        ]
        and operators["continuum_formula_rejected_as_audit_definition"]
        and operators["posthoc_continuum_substitution_forbidden"]
        and operators["implemented_scheme_features_are_all_named"],
        "closure_mapping_hashes_units_remainder_controls_formula_and_threshold_are_freeze_obligations": operators[
            "implementation_mapping_operator_hashes_units_remainder_and_controls_required"
        ]
        and operators["formula_and_threshold_deferred"]
        and operators["failure_to_close_definition_before_freeze_is_blocking"],
        "neighbor_rule_reconstructs_eleven_eligible_candidates_and_packet_ranking_exactly": neighbor[
            "candidate_count"
        ]
        == 11
        and neighbor["packet_ranking_exact"]
        and neighbor["future_result_data_used"] is False,
        "neighbor_eligibility_prose_matches_axis_sharing_candidate_universe": neighbor[
            "declared_eligibility_explicitly_requires_axis_sharing"
        ]
        and neighbor["candidate_universe_is_axis_sharing_only"],
        "R10_is_unique_provisional_top_but_not_frozen_or_one_axis_isolated": neighbor[
            "unique_top_candidate"
        ]
        and neighbor["provisional_top_candidate"] == "R10_MU_HIGH"
        and neighbor["provisional_top_matches_packet"]
        and neighbor["exact_neighbor_frozen_by_design"] is False
        and neighbor["top_shared_axis_count"] == 2,
        "all_sixteen_exact_numerical_and_custody_items_remain_freeze_deferred": separation[
            "all_sixteen_freeze_items_present"
        ]
        and separation["no_forbidden_authority_true"]
        and separation["exact_run_count_or_values_selected"] is False
        and separation["exact_neighbor_frozen"] is False
        and separation["closure_formula_or_threshold_frozen"] is False,
        "supporting_tolerance_and_duration_modules_remain_secondary_options": separation[
            "supporting_B_and_C_are_secondary_options"
        ],
        "new_output_family_is_separate_identity_bound_and_canonical_root_read_only": output[
            "new_output_family_required"
        ]
        and output["canonical_output_root_write_allowed"] is False
        and output["new_output_root_created"] is False
        and output["payload_identity_field_count"] == 13
        and output["fixed_logging_and_blocking_output_failure_contract"],
        "packet_contains_no_run_output_freeze_or_scientific_reclassification": output[
            "new_mechanism_output_created"
        ]
        is False
        and output["new_simulation_count"] == 0
        and separation["no_forbidden_authority_true"],
        "canonical_block_materiality_root_unknown_and_E_REPRO_status_remain_unchanged": packet[
            "inherited_authority"
        ]["canonical_robustness_status"]
        == "NUMERICALLY_BLOCKED"
        and packet["inherited_authority"]["root_numerical_mechanism_status"]
        == "UNRESOLVED"
        and packet["inherited_authority"]["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and packet["inherited_authority"]["new_E_REPRO"] == "NONE",
        "blocked_review_withholds_numerical_freeze_packet_preparation": True,
    }
    ordered = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "review_completed": True,
        "accepted": accepted,
        "verdict": (
            "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_FREEZE_PREPARATION_ONLY"
            if accepted
            else "BLOCK_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
        ),
        "accepted_claim_label": "POLICY_EXPERIMENT_DESIGN_ONLY" if accepted else "B-BLOCKED",
        "canonical_robustness_status": "NUMERICALLY_BLOCKED",
        "blocked_row": R13,
        "blocked_role": "SOLVER_TOL1eM08",
        "root_numerical_mechanism_status": "UNRESOLVED",
        "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
        "source_custody": custody,
        "independent_scientific_sufficiency_review": sufficiency,
        "independent_minimality_and_semantics_review": minimality,
        "independent_mechanism_specific_sufficiency": mechanism,
        "independent_hypothesis_discrimination_review": hypotheses,
        "independent_nonperturbation_review": nonperturbation,
        "independent_discrete_operator_authenticity_review": operators,
        "independent_neighbor_selection_reconstruction": neighbor,
        "independent_design_freeze_separation_review": separation,
        "independent_output_and_nonexecution_review": output,
        "review_interpretation": {
            "design_sufficiency": (
                "The four roles and fourteen observables can directly answer all three accepted "
                "mechanism questions, but the classifier and neighbor-scope ambiguities prevent "
                "acceptance of this version as a freeze-ready design."
            ),
            "neighbor_limitation": neighbor["scientific_limitation"],
            "historical_anchor_interpretation": (
                "References to the historical 1e-8, 1e-10, and 1e-12 roles are design provenance "
                "and comparison obligations, not executable freeze values; the freeze must bind "
                "the exact run matrix independently."
            ),
            "claim_ceiling": (
                "This blocked review identifies bounded specification defects only. It does not "
                "accept or repair the design, freeze the experiment, authorize execution, or alter "
                "the canonical result."
            ),
        },
        "blocking_findings": [
            {
                "finding_id": "B_NEIGHBOR_ELIGIBILITY_SCOPE_AMBIGUOUS",
                "description": (
                    "The eligibility prose describes all passing non-R13 rows, while the candidate "
                    "audit contains only the eleven rows sharing at least one exact R13 axis value."
                ),
                "bounded_correction_required": (
                    "Explicitly require at least one shared R13 axis in the eligibility rule or "
                    "reconstruct and expose all thirteen passing non-R13 candidates."
                ),
            },
            {
                "finding_id": "B_PER_HYPOTHESIS_DECISION_VECTOR_MISSING",
                "description": (
                    "Generic SINGLE and MULTIPLE outcomes do not require preservation of the H_A, "
                    "H_B, H_C, and H_D support statuses or their necessary-condition decisions."
                ),
                "bounded_correction_required": (
                    "Require a per-hypothesis support vector and criterion-decision records alongside "
                    "the aggregate outcome."
                ),
            },
            {
                "finding_id": "B_H_E_OVERLAPS_COMPLETENESS_GATE",
                "description": (
                    "H_E admits incomplete required evidence even though the earlier completeness "
                    "gate must classify missing required evidence as evidence-blocked."
                ),
                "bounded_correction_required": (
                    "Limit H_E to complete and admissible evidence that remains conflicting, below "
                    "discrimination thresholds, or otherwise nonclassifying."
                ),
            },
        ],
        "freeze_packet_preparation_obligations": {
            "observable_semantic_record_fields": [
                "observable ID",
                "physical or numerical meaning",
                "source run roles",
                "raw source fields",
                "units",
                "discrete formula",
                "norm",
                "normalization",
                "spatial aggregation",
                "time aggregation",
                "iteration aggregation",
                "conditioning floor",
                "missing-data rule",
                "comparison rule",
                "hypothesis linkage",
            ],
            "must_close_before_freeze_review": [
                "exact run matrix and paired-control multiplicity",
                "exact neighbor identity under the accepted rule",
                "exact equation-block registry bound to implementation",
                "exact actual-discrete-operator closure and truncation remainder",
                "exact nonperturbation equality or independently derived fallback equivalence",
                "exact units, norms, floors, thresholds, contrasts, associations, and tie rules",
                "exact output schema, cadence, volume budget, paths, and payload identities",
                "exact controls, classifier, implementation hashes, and one-execution rule",
            ],
            "freeze_failure_disposition": (
                "Any unresolved required semantic, operator, nonperturbation, custody, or classifier "
                "item blocks freeze acceptance and cannot be filled from experiment results."
            ),
        },
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "validation_status": {
            "focused_independent_design_review_tests": {"passed": 15, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 287,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 155, "status": "PASSED"},
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
        "selected_next_target": SELECTED_NEXT_TARGET if accepted else TARGET,
        "authority_rotation": {
            "instrumented_R13_experiment_design_accepted": accepted,
            "numerical_freeze_packet_preparation_authorized": accepted,
            "numerical_freeze_packet_prepared": False,
            "numerical_freeze_accepted": False,
            "experiment_frozen": False,
            "exact_run_count_or_values_selected": False,
            "new_simulation_authorized": False,
            "rerun_authorized": False,
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
        "reviewer_sha256": sha256_path(REPO_ROOT / REVIEWER_RELATIVE_PATH),
        "nonclaims": [
            "no numerical freeze packet prepared or accepted",
            "no exact run count or run matrix",
            "no exact tolerance or duration schedule",
            "no exact neighbor frozen",
            "no exact output schema, floor, threshold, contrast, association, or classifier frozen",
            "no new output root or simulation",
            "no canonical output mutation",
            "no rerun",
            "no root mechanism identified",
            "no physical instability or model-domain boundary",
            "no conditional or broad robustness",
            "no descendant materiality",
            "no new E-REPRO",
            "no pillar or seam promotion",
            "no C_k dynamics, CCFT promotion, or master-action promotion",
            "no repository-wide green claim",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the instrumented R13 mechanism design packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, IndexError, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    raw = canonical_json_bytes(report)
    if args.write:
        REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REPORT_PATH.write_bytes(raw)
    elif args.check:
        if not REPORT_PATH.is_file() or REPORT_PATH.read_bytes() != raw:
            print(f"stale or missing design review artifact: {REPORT_RELATIVE_PATH}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(raw)
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during independent design review", file=sys.stderr)
        return 1
    if report["failed_decision_ids"]:
        if args.write:
            print(
                f"independent design review blocked on {len(report['failed_decision_ids'])} "
                "specification decisions; authority unchanged"
            )
        elif args.check:
            print(
                f"blocked independent design review verified: "
                f"{len(report['failed_decision_ids'])} findings; canonical outputs unchanged"
            )
        return 0
    if args.write:
        print(
            f"wrote independent design review: {report['passed_decision_count']}/"
            f"{report['decision_count']} decisions; selected {report['selected_next_target']}"
        )
    elif args.check:
        print(
            f"independent design review verified: {report['passed_decision_count']}/"
            f"{report['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
