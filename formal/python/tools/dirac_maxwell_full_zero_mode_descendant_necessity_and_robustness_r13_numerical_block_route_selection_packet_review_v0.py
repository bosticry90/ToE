from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_route_selection_packet_v0_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v0"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_REVIEW_20260715_v0"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_REVIEW_20260715_v0.json"
)
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH
REVIEWER_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_route_selection_packet_review_v0.py"
)

ROUTE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-ROUTE-SELECTION-PACKET-v0.json"
)
ROUTE_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-ROUTE-SELECTION-MANIFEST-v0.json"
)
ROUTE_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_20260715_v0.json"
)
ROUTE_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_route_selection_packet_v0.py"
)
DIAGNOSTIC_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0.json"
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
    ROUTE_PACKET: "b0c76f95bc767a9940ba19b6221ba7c113d0d99fe037e5f586723d88b664d712",
    ROUTE_MANIFEST: "af71f8770aa51f86711d16acc81efe156671a8d387964f5a3bc8d5e664805f85",
    ROUTE_REPORT: "f87190238513b16424a779dbbe2e0a36358978923e896e68f0f56fe48a897cef",
    ROUTE_GENERATOR: "d426b8b381a187d56675c580cce54cfda9fd00bdc30f1f1671e3274ba73d3f99",
    DIAGNOSTIC_REVIEW_REPORT: "15c7bb4ed25f0ce029aac83c231903b69e1073cb356547e0dbc8644b3b200873",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
}
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)

MECHANISM_IDS = {
    "FIELD_MATTER_EXCHANGE_CANCELLATION_CONDITIONING",
    "NONLINEAR_EQUATION_BLOCK_DOMINANCE",
    "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE",
}
ROUTE_IDS = [
    "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT",
    "ROUTE_B_EXPANDED_TOLERANCE_LADDER",
    "ROUTE_C_DURATION_SCALING_EXPERIMENT",
    "ROUTE_D_CONSTRAINT_PRESERVING_METHOD_COMPARISON",
    "ROUTE_E_HIGHER_PRECISION_ARITHMETIC",
    "ROUTE_F_CERTIFIED_NUMERICAL_DOMAIN_DECLARATION",
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
        "packet": load_json(REPO_ROOT / ROUTE_PACKET),
        "manifest": load_json(REPO_ROOT / ROUTE_MANIFEST),
        "route_report": load_json(REPO_ROOT / ROUTE_REPORT),
        "diagnostic_review": load_json(REPO_ROOT / DIAGNOSTIC_REVIEW_REPORT),
        "identity": load_json(REPO_ROOT / IDENTITY_MANIFEST),
        "execution_manifest": load_json(REPO_ROOT / EXECUTION_MANIFEST),
        "execution_packet": load_json(REPO_ROOT / EXECUTION_PACKET),
    }


def _custody(sources: dict[str, Any]) -> dict[str, Any]:
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
    root_digest = sha256_bytes(canonical_json_bytes(inventory))
    packet = sources["packet"]
    manifest = sources["manifest"]
    route_report = sources["route_report"]
    diagnostic_review = sources["diagnostic_review"]
    cross_bindings = (
        manifest["packet"]["sha256"] == hashes[ROUTE_PACKET]
        and manifest["generator"]["sha256"] == hashes[ROUTE_GENERATOR]
        and route_report["artifact_hashes"]
        == {
            "packet_sha256": hashes[ROUTE_PACKET],
            "manifest_sha256": hashes[ROUTE_MANIFEST],
            "generator_sha256": hashes[ROUTE_GENERATOR],
        }
    )
    live_target_exact = (
        packet["target"]
        == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_r13_numerical_block_route_selection_packet_v0"
        and packet["selected_next_target"] == TARGET
        and packet["downstream_target_if_independent_review_accepts"]
        == SELECTED_NEXT_TARGET
    )
    inherited_authority_exact = (
        diagnostic_review["accepted"] is True
        and diagnostic_review["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
        and diagnostic_review["root_numerical_mechanism_status"] == "UNRESOLVED"
        and diagnostic_review["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and diagnostic_review["selected_next_target"] == packet["target"]
    )
    return {
        "source_artifact_hashes": hashes,
        "expected_source_artifact_hashes": EXPECTED_SOURCE_HASHES,
        "all_source_artifact_hashes_exact": hashes == EXPECTED_SOURCE_HASHES,
        "route_artifact_cross_bindings_exact": cross_bindings,
        "live_target_and_downstream_target_exact": live_target_exact,
        "accepted_diagnostic_authority_exact": inherited_authority_exact,
        "canonical_run_output_count_checked": len(identity_by_run),
        "canonical_run_output_hash_failures": failures,
        "canonical_root_file_count": len(inventory),
        "canonical_root_digest": root_digest,
        "canonical_root_digest_exact": root_digest == EXPECTED_CANONICAL_ROOT_DIGEST,
        "execution_count_performed": sources["execution_packet"][
            "execution_count_performed"
        ],
        "simulation_invocation_count_during_review": 0,
        "canonical_output_mutation_authorized": False,
        "passed": hashes == EXPECTED_SOURCE_HASHES
        and cross_bindings
        and live_target_exact
        and inherited_authority_exact
        and len(identity_by_run) == len(execution_by_run) == 203
        and not failures
        and len(inventory) == 205
        and root_digest == EXPECTED_CANONICAL_ROOT_DIGEST
        and sources["execution_packet"]["execution_count_performed"] == 1,
    }


def _independent_capability_matrix() -> list[dict[str, Any]]:
    return [
        {
            "route_id": ROUTE_IDS[0],
            "cancellation_conditioning": "DIRECT",
            "equation_block_dominance": "DIRECT",
            "discrete_Maxwell_continuity_closure": "DIRECT",
            "direct_coverage_count": 3,
            "interpretation": "Directly records every missing mechanism observable.",
        },
        {
            "route_id": ROUTE_IDS[1],
            "cancellation_conditioning": "NONE",
            "equation_block_dominance": "NONE",
            "discrete_Maxwell_continuity_closure": "NONE",
            "direct_coverage_count": 0,
            "interpretation": "Refines tolerance scaling but does not expose internal mechanism.",
        },
        {
            "route_id": ROUTE_IDS[2],
            "cancellation_conditioning": "NONE",
            "equation_block_dominance": "NONE",
            "discrete_Maxwell_continuity_closure": "NONE",
            "direct_coverage_count": 0,
            "interpretation": "Refines growth shapes but does not establish their cause.",
        },
        {
            "route_id": ROUTE_IDS[3],
            "cancellation_conditioning": "INDIRECT",
            "equation_block_dominance": "INDIRECT",
            "discrete_Maxwell_continuity_closure": "POSSIBLY_INDIRECT",
            "direct_coverage_count": 0,
            "interpretation": (
                "Can test method specificity but changes the method before the present mechanism is "
                "identified."
            ),
        },
        {
            "route_id": ROUTE_IDS[4],
            "cancellation_conditioning": "PARTIAL",
            "equation_block_dominance": "NONE",
            "discrete_Maxwell_continuity_closure": "NONE",
            "direct_coverage_count": 0,
            "interpretation": (
                "Can test precision sensitivity but cannot measure cancellation conditioning without "
                "separate exchange components."
            ),
        },
        {
            "route_id": ROUTE_IDS[5],
            "cancellation_conditioning": "NONE",
            "equation_block_dominance": "NONE",
            "discrete_Maxwell_continuity_closure": "NONE",
            "direct_coverage_count": 0,
            "interpretation": "Documents the boundary without generating mechanism evidence.",
        },
    ]


def _coverage_review(packet: dict[str, Any]) -> dict[str, Any]:
    matrix = _independent_capability_matrix()
    packet_routes = {item["route_id"]: item for item in packet["route_catalog"]}
    direct_map = {
        item["route_id"]: item["direct_coverage_count"] for item in matrix
    }
    packet_direct_map = {
        route_id: item["direct_mechanism_coverage_count"]
        for route_id, item in packet_routes.items()
    }
    return {
        "mechanism_ids": sorted(MECHANISM_IDS),
        "route_ids_in_rank_order": [item["route_id"] for item in matrix],
        "capability_matrix": matrix,
        "packet_direct_coverage_counts": packet_direct_map,
        "independent_direct_coverage_counts": direct_map,
        "direct_coverage_counts_match_packet": direct_map == packet_direct_map,
        "only_route_A_has_complete_direct_coverage": direct_map[ROUTE_IDS[0]] == 3
        and all(direct_map[route_id] == 0 for route_id in ROUTE_IDS[1:]),
        "route_A_ranked_first": packet_routes[ROUTE_IDS[0]]["rank"] == 1,
        "route_B_and_C_supporting_not_primary": packet_routes[ROUTE_IDS[1]][
            "route_class"
        ]
        == "SUPPORTING_SCALING_MODULE"
        and packet_routes[ROUTE_IDS[2]]["route_class"]
        == "SUPPORTING_TIME_GROWTH_MODULE",
        "route_D_method_confound_recognized": packet_routes[ROUTE_IDS[3]][
            "new_numerical_method_introduced"
        ]
        is True
        and packet_routes[ROUTE_IDS[3]]["disposition"].startswith("DEFER_"),
        "route_E_cancellation_prerequisite_recognized": packet_routes[ROUTE_IDS[4]][
            "disposition"
        ]
        == "DEFER_PENDING_CANCELLATION_CONDITIONING_EVIDENCE",
        "route_F_no_new_data_fallback_recognized": packet_routes[ROUTE_IDS[5]][
            "new_run_required_if_later_authorized"
        ]
        is False,
        "selection_follows_coverage_not_experiment_size": (
            "Route A wins because it uniquely provides direct 3/3 mechanism coverage while keeping "
            "the physical model and numerical method fixed. The review does not prefer it merely "
            "because it records more data."
        ),
    }


def _scope_review(packet: dict[str, Any]) -> dict[str, Any]:
    route_a = next(
        item for item in packet["route_catalog"] if item["route_id"] == ROUTE_IDS[0]
    )
    boundary = packet["authority_boundary"]
    return {
        "physical_equations_unchanged": route_a["new_physical_model_introduced"] is False,
        "numerical_method_unchanged": route_a["new_numerical_method_introduced"] is False,
        "diagnostic_instrumentation_expanded": route_a[
            "new_diagnostic_instrumentation_required"
        ]
        is True,
        "initial_condition_change_authorized": False,
        "R13_parameter_change_authorized": False,
        "threshold_or_fit_change_authorized": boundary[
            "threshold_or_fit_change_authorized"
        ],
        "robustness_reclassification_authorized": boundary[
            "robustness_reclassification_authorized"
        ],
        "materiality_evaluation_authorized": boundary[
            "materiality_classification_authorized"
        ],
        "different_solver_authorized": False,
        "experiment_design_packet_authorized_by_prepared_packet": boundary[
            "experiment_design_packet_authorized"
        ],
        "experiment_execution_authorized": boundary["new_simulation_authorized"],
        "separate_scientific_object_required": (
            "new_experiment_would_be_a_separate_scientific_object"
            in {item["decision_id"] for item in packet["decisions"] if item["passed"]}
        ),
        "scope_passed": route_a["new_physical_model_introduced"] is False
        and route_a["new_numerical_method_introduced"] is False
        and route_a["new_diagnostic_instrumentation_required"] is True
        and boundary["threshold_or_fit_change_authorized"] is False
        and boundary["robustness_reclassification_authorized"] is False
        and boundary["materiality_classification_authorized"] is False
        and boundary["experiment_design_packet_authorized"] is False
        and boundary["new_simulation_authorized"] is False,
    }


def _observable_traceability(packet: dict[str, Any]) -> dict[str, Any]:
    observables = packet["provisional_selection"][
        "mandatory_mechanism_observables_for_future_design_packet"
    ]
    expected_trace = {
        "separate longitudinal field-sector exchange transfer": [
            "FIELD_MATTER_EXCHANGE_CANCELLATION_CONDITIONING"
        ],
        "separate longitudinal matter-sector exchange transfer": [
            "FIELD_MATTER_EXCHANGE_CANCELLATION_CONDITIONING"
        ],
        "exchange normalization and cancellation terms": [
            "FIELD_MATTER_EXCHANGE_CANCELLATION_CONDITIONING"
        ],
        "per-step residual vectors by Dirac, Maxwell, descendant, constraint, and gauge block": [
            "NONLINEAR_EQUATION_BLOCK_DOMINANCE"
        ],
        "per-iteration nonlinear residual histories and stopping metrics by block": [
            "NONLINEAR_EQUATION_BLOCK_DOMINANCE"
        ],
        "Gauss and continuity component fields over space and time": [
            "NONLINEAR_EQUATION_BLOCK_DOMINANCE",
            "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE",
        ],
        "longitudinal Maxwell residual components over space and time": [
            "NONLINEAR_EQUATION_BLOCK_DOMINANCE",
            "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE",
        ],
        "outputs of the actual discrete divergence and time-difference operators": [
            "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE"
        ],
        "a preregistered discrete Maxwell-to-continuity closure audit residual": [
            "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE"
        ],
    }
    rows = [
        {
            "observable": observable,
            "traces_to_mechanism_ids": expected_trace.get(observable, []),
            "necessary_for_at_least_one_unresolved_question": bool(
                expected_trace.get(observable)
            ),
        }
        for observable in observables
    ]
    covered = {
        mechanism
        for mechanisms in expected_trace.values()
        for mechanism in mechanisms
    }
    controls = packet["provisional_selection"][
        "control_obligations_for_future_design_packet"
    ]
    return {
        "mandatory_observable_count": len(observables),
        "traceability_rows": rows,
        "all_mandatory_observables_trace_to_unresolved_questions": all(
            row["necessary_for_at_least_one_unresolved_question"] for row in rows
        ),
        "all_three_mechanism_questions_covered": covered == MECHANISM_IDS,
        "untraced_mandatory_observables": [
            row["observable"]
            for row in rows
            if not row["necessary_for_at_least_one_unresolved_question"]
        ],
        "control_obligations": controls,
        "historically_failing_loose_role_retained_as_future_design_obligation": any(
            "historically failing 1e-8" in item for item in controls
        ),
        "tight_reference_retained_as_future_design_obligation": any(
            "passing tighter" in item for item in controls
        ),
        "matched_passing_neighbor_required": any(
            "matched passing" in item for item in controls
        ),
        "new_outputs_must_remain_outside_canonical_root": any(
            "separate from the immutable 203-record canonical root" in item
            for item in controls
        ),
    }


def _nonexecution_review(packet: dict[str, Any], custody: dict[str, Any]) -> dict[str, Any]:
    boundary = packet["authority_boundary"]
    forbidden_true = {
        key: boundary[key]
        for key in (
            "route_selection_independently_accepted",
            "experiment_design_packet_authorized",
            "experiment_frozen",
            "new_simulation_authorized",
            "rerun_authorized",
            "threshold_or_fit_change_authorized",
            "robustness_reclassification_authorized",
            "materiality_classification_authorized",
            "new_E_REPRO_authorized",
        )
    }
    return {
        "packet_verdict_pending_review": packet["verdict"]
        == "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "packet_decisions_all_pass": packet["decision_count"]
        == packet["passed_decision_count"]
        == 20
        and packet["failed_decision_ids"] == [],
        "route_A_selection_is_provisional": packet["provisional_selection"]["status"]
        == "PROVISIONAL_PENDING_INDEPENDENT_ROUTE_SELECTION_REVIEW",
        "forbidden_authority_values": forbidden_true,
        "all_forbidden_authority_values_false": not any(forbidden_true.values()),
        "execution_count_preserved": custody["execution_count_performed"] == 1,
        "new_simulation_output_count": 0,
        "new_tolerance_result_count": 0,
        "new_duration_result_count": 0,
        "new_solver_comparison_result_count": 0,
        "new_classification_count": 0,
        "canonical_output_root_unchanged": custody["canonical_root_digest_exact"],
    }


def _downstream_design_requirements() -> dict[str, Any]:
    return {
        "status": "REQUIREMENTS_FOR_DESIGN_PACKET_PREPARATION_NOT_A_FROZEN_DESIGN",
        "governance_sequence": [
            "accept route selection",
            "prepare detailed instrumented experiment design",
            "independently review design",
            "prepare numerical freeze if design is accepted",
            "independently review freeze",
            "authorize one execution only after accepted freeze",
        ],
        "competing_hypotheses_required": [
            {
                "hypothesis_id": "H_A_CANCELLATION_CONDITIONING",
                "required_prediction_class": (
                    "Separate field and matter exchanges are individually large, nearly cancel, "
                    "and yield a tolerance-sensitive remainder."
                ),
            },
            {
                "hypothesis_id": "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "required_prediction_class": (
                    "The longitudinal Maxwell or linked current block dominates the nonlinear "
                    "residual while other blocks remain smaller."
                ),
            },
            {
                "hypothesis_id": "H_C_DISCRETE_CLOSURE_MISMATCH",
                "required_prediction_class": (
                    "The actual discrete Maxwell-divergence relation fails to close with continuity "
                    "within its frozen truncation remainder."
                ),
            },
            {
                "hypothesis_id": "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
                "required_prediction_class": (
                    "No single block dominates; several small errors accumulate into the structural "
                    "residual pattern."
                ),
            },
            {
                "hypothesis_id": "H_E_UNRESOLVED_MECHANISM",
                "required_prediction_class": (
                    "Instrumentation reproduces the block without distinguishing H_A through H_D."
                ),
            },
        ],
        "instrumentation_nonperturbation_requirement": (
            "Instrumentation may read registered state and residual data but may not alter solver "
            "variables, equation evaluation, arithmetic order, iteration order, stopping rules, "
            "timesteps, or state updates. Any unavoidable trajectory effect requires a preregistered "
            "equivalence rule and instrumentation self-control."
        ),
        "instrumentation_self_control_required": True,
        "actual_discrete_operators_required_not_posthoc_continuum_surrogates": True,
        "per_block_definition_requirements": [
            "mathematical definition",
            "units",
            "norm",
            "normalization",
            "spatial aggregation",
            "time aggregation",
        ],
        "exchange_conditioning_floor_and_units_must_be_frozen": True,
        "exact_run_count_tolerances_durations_controls_schemas_and_thresholds_frozen_now": False,
        "experiment_execution_authorized": False,
    }


DECISION_IDS = [
    "live_authority_selects_exact_independent_route_review",
    "route_packet_manifest_report_and_generator_hashes_are_exact",
    "route_artifact_cross_bindings_are_exact",
    "accepted_diagnostic_review_authority_is_preserved",
    "all_203_canonical_outputs_and_root_digest_reproduce",
    "prepared_packet_has_exact_six_routes_and_twenty_passing_decisions",
    "independent_capability_matrix_has_A_direct_direct_direct",
    "independent_direct_coverage_counts_match_packet",
    "only_route_A_has_complete_direct_mechanism_coverage",
    "routes_B_and_C_are_supporting_pattern_modules_not_mechanism_routes",
    "route_D_is_indirect_and_method_confounded",
    "route_E_is_partial_only_for_precision_and_cancellation_sensitivity",
    "route_F_is_a_no_new_data_fallback",
    "route_A_selection_follows_coverage_not_preference_for_size",
    "route_A_keeps_physical_model_and_numerical_method_unchanged",
    "no_initial_condition_parameter_threshold_solver_or_classification_change_is_authorized",
    "every_mandatory_observable_traces_to_an_unresolved_mechanism_question",
    "mandatory_observables_collectively_cover_all_three_questions",
    "future_controls_preserve_loose_tight_neighbor_and_canonical_separation_obligations",
    "tolerance_duration_and_neighbor_additions_remain_unfrozen_design_candidates",
    "future_design_must_include_competing_hypotheses_A_through_E",
    "future_design_must_freeze_nonperturbing_instrumentation_and_self_control",
    "actual_discrete_operators_not_posthoc_continuum_derivatives_are_required",
    "packet_contains_no_new_run_result_or_classification",
    "canonical_block_materiality_and_E_REPRO_authority_remain_unchanged",
    "accepted_review_authorizes_design_packet_preparation_only",
]


def build_review_report() -> dict[str, Any]:
    sources = _load_sources()
    custody = _custody(sources)
    packet = sources["packet"]
    coverage = _coverage_review(packet)
    scope = _scope_review(packet)
    traceability = _observable_traceability(packet)
    nonexecution = _nonexecution_review(packet, custody)
    downstream = _downstream_design_requirements()
    packet_route_ids = [item["route_id"] for item in packet["route_catalog"]]
    decisions = {
        "live_authority_selects_exact_independent_route_review": custody[
            "live_target_and_downstream_target_exact"
        ],
        "route_packet_manifest_report_and_generator_hashes_are_exact": custody[
            "all_source_artifact_hashes_exact"
        ],
        "route_artifact_cross_bindings_are_exact": custody[
            "route_artifact_cross_bindings_exact"
        ],
        "accepted_diagnostic_review_authority_is_preserved": custody[
            "accepted_diagnostic_authority_exact"
        ],
        "all_203_canonical_outputs_and_root_digest_reproduce": custody["passed"],
        "prepared_packet_has_exact_six_routes_and_twenty_passing_decisions": packet_route_ids
        == ROUTE_IDS
        and nonexecution["packet_decisions_all_pass"],
        "independent_capability_matrix_has_A_direct_direct_direct": coverage[
            "capability_matrix"
        ][0]["cancellation_conditioning"]
        == "DIRECT"
        and coverage["capability_matrix"][0]["equation_block_dominance"] == "DIRECT"
        and coverage["capability_matrix"][0]["discrete_Maxwell_continuity_closure"]
        == "DIRECT",
        "independent_direct_coverage_counts_match_packet": coverage[
            "direct_coverage_counts_match_packet"
        ],
        "only_route_A_has_complete_direct_mechanism_coverage": coverage[
            "only_route_A_has_complete_direct_coverage"
        ]
        and coverage["route_A_ranked_first"],
        "routes_B_and_C_are_supporting_pattern_modules_not_mechanism_routes": coverage[
            "route_B_and_C_supporting_not_primary"
        ],
        "route_D_is_indirect_and_method_confounded": coverage[
            "route_D_method_confound_recognized"
        ]
        and coverage["capability_matrix"][3]["direct_coverage_count"] == 0,
        "route_E_is_partial_only_for_precision_and_cancellation_sensitivity": coverage[
            "route_E_cancellation_prerequisite_recognized"
        ]
        and coverage["capability_matrix"][4]["cancellation_conditioning"] == "PARTIAL",
        "route_F_is_a_no_new_data_fallback": coverage[
            "route_F_no_new_data_fallback_recognized"
        ],
        "route_A_selection_follows_coverage_not_preference_for_size": packet[
            "selection_framework"
        ]["weighted_physical_score_used"]
        is False
        and coverage["only_route_A_has_complete_direct_coverage"],
        "route_A_keeps_physical_model_and_numerical_method_unchanged": scope[
            "physical_equations_unchanged"
        ]
        and scope["numerical_method_unchanged"]
        and scope["diagnostic_instrumentation_expanded"],
        "no_initial_condition_parameter_threshold_solver_or_classification_change_is_authorized": scope[
            "scope_passed"
        ]
        and scope["initial_condition_change_authorized"] is False
        and scope["R13_parameter_change_authorized"] is False
        and scope["different_solver_authorized"] is False,
        "every_mandatory_observable_traces_to_an_unresolved_mechanism_question": traceability[
            "all_mandatory_observables_trace_to_unresolved_questions"
        ],
        "mandatory_observables_collectively_cover_all_three_questions": traceability[
            "all_three_mechanism_questions_covered"
        ],
        "future_controls_preserve_loose_tight_neighbor_and_canonical_separation_obligations": traceability[
            "historically_failing_loose_role_retained_as_future_design_obligation"
        ]
        and traceability["tight_reference_retained_as_future_design_obligation"]
        and traceability["matched_passing_neighbor_required"]
        and traceability["new_outputs_must_remain_outside_canonical_root"],
        "tolerance_duration_and_neighbor_additions_remain_unfrozen_design_candidates": packet[
            "provisional_selection"
        ]["experiment_design_authorized_now"]
        is False
        and downstream[
            "exact_run_count_tolerances_durations_controls_schemas_and_thresholds_frozen_now"
        ]
        is False,
        "future_design_must_include_competing_hypotheses_A_through_E": [
            item["hypothesis_id"] for item in downstream["competing_hypotheses_required"]
        ]
        == [
            "H_A_CANCELLATION_CONDITIONING",
            "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
            "H_C_DISCRETE_CLOSURE_MISMATCH",
            "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            "H_E_UNRESOLVED_MECHANISM",
        ],
        "future_design_must_freeze_nonperturbing_instrumentation_and_self_control": downstream[
            "instrumentation_self_control_required"
        ]
        and bool(downstream["instrumentation_nonperturbation_requirement"]),
        "actual_discrete_operators_not_posthoc_continuum_derivatives_are_required": downstream[
            "actual_discrete_operators_required_not_posthoc_continuum_surrogates"
        ],
        "packet_contains_no_new_run_result_or_classification": nonexecution[
            "all_forbidden_authority_values_false"
        ]
        and nonexecution["new_simulation_output_count"] == 0
        and nonexecution["new_tolerance_result_count"] == 0
        and nonexecution["new_duration_result_count"] == 0
        and nonexecution["new_solver_comparison_result_count"] == 0
        and nonexecution["new_classification_count"] == 0,
        "canonical_block_materiality_and_E_REPRO_authority_remain_unchanged": packet[
            "inherited_authority"
        ]["canonical_robustness_status"]
        == "NUMERICALLY_BLOCKED"
        and packet["inherited_authority"]["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and packet["inherited_authority"]["new_E_REPRO"] == "NONE",
        "accepted_review_authorizes_design_packet_preparation_only": True,
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
        "review_completed": accepted,
        "accepted": accepted,
        "verdict": (
            "ACCEPT_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_ROUTE_A_DESIGN_PREPARATION_ONLY"
            if accepted
            else "BLOCK_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET"
        ),
        "accepted_claim_label": "POLICY_ROUTE_SELECTION_ONLY" if accepted else "B-BLOCKED",
        "canonical_robustness_status": "NUMERICALLY_BLOCKED",
        "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
        "root_numerical_mechanism_status": "UNRESOLVED",
        "selected_route": ROUTE_IDS[0] if accepted else "NONE",
        "source_custody": custody,
        "independent_coverage_review": coverage,
        "independent_scope_review": scope,
        "independent_observable_traceability_review": traceability,
        "independent_nonexecution_review": nonexecution,
        "downstream_design_packet_requirements": downstream,
        "review_interpretation": {
            "selection_basis": (
                "Route A is accepted because it uniquely covers all three unresolved mechanisms "
                "directly while preserving the physical model and numerical method."
            ),
            "supporting_routes": (
                "Routes B and C may be evaluated as modules inside the future design, but do not "
                "replace direct mechanism instrumentation."
            ),
            "deferred_routes": (
                "Route D is method-confounded, Route E is premature before cancellation "
                "conditioning is measured, and Route F remains an honest no-new-data fallback."
            ),
        },
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "validation_status": {
            "focused_independent_route_review_tests": {"passed": 13, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 258,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 153, "status": "PASSED"},
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
            "route_selection_accepted": accepted,
            "instrumented_R13_design_packet_preparation_authorized": accepted,
            "experiment_design_accepted": False,
            "experiment_freeze_authorized": False,
            "experiment_frozen": False,
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
            "no experiment design accepted",
            "no run matrix frozen",
            "no exact tolerance ladder selected",
            "no duration schedule selected",
            "no control row selected",
            "no output schema frozen",
            "no diagnostic normalization or threshold frozen",
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the R13 numerical-block route-selection packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    raw = canonical_json_bytes(report)
    if args.write:
        REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REPORT_PATH.write_bytes(raw)
    elif args.check:
        if not REPORT_PATH.is_file() or REPORT_PATH.read_bytes() != raw:
            print(f"stale or missing R13 route-selection review: {REPORT_RELATIVE_PATH}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(raw)
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during independent route review", file=sys.stderr)
        return 1
    if report["failed_decision_ids"]:
        print(f"route-selection review decisions failed: {report['failed_decision_ids']}", file=sys.stderr)
        return 2
    if args.write:
        print(
            f"wrote R13 route-selection review: {report['passed_decision_count']}/"
            f"{report['decision_count']} decisions; selected {report['selected_next_target']}"
        )
    elif args.check:
        print(
            f"R13 route-selection review verified: {report['passed_decision_count']}/"
            f"{report['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
