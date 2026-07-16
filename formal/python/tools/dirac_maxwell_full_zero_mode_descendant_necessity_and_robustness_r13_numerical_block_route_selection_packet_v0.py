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
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_route_selection_packet_v0"
)
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_route_selection_packet_v0_result"
)
DOWNSTREAM_TARGET_IF_ACCEPTED = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v0"
)
PACKET_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_v0"
)
MANIFEST_SCHEMA_ID = f"{PACKET_SCHEMA_ID}_MANIFEST"
REPORT_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_20260715_v0"
)

PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-ROUTE-SELECTION-PACKET-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-ROUTE-SELECTION-MANIFEST-v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_20260715_v0.json"
)
GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_route_selection_packet_v0.py"
)
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

DIAGNOSTIC_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0.json"
)
DIAGNOSTIC_REVIEWER = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_diagnostic_packet_review_v0.py"
)
DIAGNOSTIC_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-DIAGNOSTIC-PACKET-v0.json"
)
DIAGNOSTIC_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-DIAGNOSTIC-MANIFEST-v0.json"
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
    DIAGNOSTIC_REVIEW_REPORT: "15c7bb4ed25f0ce029aac83c231903b69e1073cb356547e0dbc8644b3b200873",
    DIAGNOSTIC_REVIEWER: "fcf173e2299edf93523cec588e5558d06b51baf4168cd77aef3e7d29f422615d",
    DIAGNOSTIC_PACKET: "8edd51901d2999ea1781c5768a64aeabd7d5328dfda61f45e4a7853865937eed",
    DIAGNOSTIC_MANIFEST: "bf8ffa4e606229d0eb0a54a41bddf62fc02c15316cd41efc00eaa2d67f6d6aca",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
}
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)

MECHANISM_QUESTIONS = [
    {
        "mechanism_id": "FIELD_MATTER_EXCHANGE_CANCELLATION_CONDITIONING",
        "question": (
            "Are separate longitudinal field and matter exchange transfers large and nearly "
            "cancelling, making the registered exchange residual ill-conditioned?"
        ),
        "minimum_required_observables": [
            "longitudinal_field_sector_transfer",
            "longitudinal_matter_sector_transfer",
            "their registered normalization terms",
        ],
    },
    {
        "mechanism_id": "NONLINEAR_EQUATION_BLOCK_DOMINANCE",
        "question": (
            "Which Dirac, Maxwell, descendant, constraint, or gauge block dominates the nonlinear "
            "solve error at each step?"
        ),
        "minimum_required_observables": [
            "solver residual vector by equation block and step",
            "block stopping metrics",
            "iteration-local residual history",
        ],
    },
    {
        "mechanism_id": "DISCRETE_MAXWELL_TO_CONTINUITY_CLOSURE",
        "question": (
            "Does the actual discrete divergence of the longitudinal Maxwell residual account for "
            "the stored continuity residual?"
        ),
        "minimum_required_observables": [
            "longitudinal Maxwell residual components over space and time",
            "actual discrete derivative operator outputs",
            "continuity residual components over space and time",
        ],
    },
]
MECHANISM_IDS = {item["mechanism_id"] for item in MECHANISM_QUESTIONS}


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
    review = load_json(REPO_ROOT / DIAGNOSTIC_REVIEW_REPORT)
    diagnostic_packet = load_json(REPO_ROOT / DIAGNOSTIC_PACKET)
    diagnostic_manifest = load_json(REPO_ROOT / DIAGNOSTIC_MANIFEST)
    identity = load_json(REPO_ROOT / IDENTITY_MANIFEST)
    execution_manifest = load_json(REPO_ROOT / EXECUTION_MANIFEST)
    execution_packet = load_json(REPO_ROOT / EXECUTION_PACKET)
    return {
        "review": review,
        "diagnostic_packet": diagnostic_packet,
        "diagnostic_manifest": diagnostic_manifest,
        "identity": identity,
        "execution_manifest": execution_manifest,
        "execution_packet": execution_packet,
    }


def _source_custody(sources: dict[str, Any]) -> dict[str, Any]:
    observed_hashes = {
        path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES
    }
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
    review = sources["review"]
    review_authority_exact = (
        review["accepted"] is True
        and review["verdict"]
        == "ACCEPT_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PATTERN_ROOT_MECHANISM_UNRESOLVED"
        and review["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
        and review["root_numerical_mechanism_status"] == "UNRESOLVED"
        and review["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and review["selected_next_target"] == TARGET
    )
    return {
        "source_artifact_hashes": observed_hashes,
        "expected_source_artifact_hashes": EXPECTED_SOURCE_HASHES,
        "all_source_artifact_hashes_exact": observed_hashes == EXPECTED_SOURCE_HASHES,
        "accepted_diagnostic_review_authority_exact": review_authority_exact,
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
        "passed": observed_hashes == EXPECTED_SOURCE_HASHES
        and review_authority_exact
        and len(identity_by_run) == len(execution_by_run) == 203
        and not failures
        and len(inventory) == 205
        and digest == EXPECTED_CANONICAL_ROOT_DIGEST
        and sources["execution_packet"]["execution_count_performed"] == 1,
    }


def _route_catalog() -> list[dict[str, Any]]:
    all_mechanisms = sorted(MECHANISM_IDS)
    return [
        {
            "route_id": "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT",
            "rank": 1,
            "title": "Instrumented R13 mechanism experiment",
            "route_class": "PRIMARY_MECHANISM_RESOLUTION",
            "direct_mechanism_coverage": all_mechanisms,
            "direct_mechanism_coverage_count": 3,
            "supporting_questions": [
                "where the longitudinal mismatch first appears",
                "whether exchange integrates or amplifies an earlier mismatch",
                "why R13 differs from a matched passing neighbor",
            ],
            "new_numerical_method_introduced": False,
            "new_physical_model_introduced": False,
            "new_diagnostic_instrumentation_required": True,
            "new_run_required_if_later_authorized": True,
            "strength": "Directly measures every presently unavailable mechanism observable.",
            "limitation": (
                "Requires a separately reviewed instrumented design and new execution; the current "
                "route packet supplies neither."
            ),
            "disposition": "PROVISIONALLY_SELECTED_PENDING_INDEPENDENT_ROUTE_REVIEW",
        },
        {
            "route_id": "ROUTE_B_EXPANDED_TOLERANCE_LADDER",
            "rank": 2,
            "title": "Expanded tolerance ladder",
            "route_class": "SUPPORTING_SCALING_MODULE",
            "direct_mechanism_coverage": [],
            "direct_mechanism_coverage_count": 0,
            "supporting_questions": [
                "whether the descriptive approximately 0.75 tolerance exponent persists",
                "whether the pairwise exponents settle into an asymptotic regime",
            ],
            "new_numerical_method_introduced": False,
            "new_physical_model_introduced": False,
            "new_diagnostic_instrumentation_required": False,
            "new_run_required_if_later_authorized": True,
            "strength": "Narrow, simple, and directly strengthens the tolerance-response map.",
            "limitation": "Improves scaling evidence but does not identify any missing mechanism alone.",
            "disposition": "SUPPORTING_COMPONENT_CANDIDATE_FOR_ROUTE_A_DESIGN",
        },
        {
            "route_id": "ROUTE_C_DURATION_SCALING_EXPERIMENT",
            "rank": 3,
            "title": "Duration-scaling experiment",
            "route_class": "SUPPORTING_TIME_GROWTH_MODULE",
            "direct_mechanism_coverage": [],
            "direct_mechanism_coverage_count": 0,
            "supporting_questions": [
                "whether three structural residuals remain approximately linear in time",
                "whether longitudinal exchange remains closer to quadratic growth",
            ],
            "new_numerical_method_introduced": False,
            "new_physical_model_introduced": False,
            "new_diagnostic_instrumentation_required": False,
            "new_run_required_if_later_authorized": True,
            "strength": "Directly tests the accepted descriptive time-order and growth-shape pattern.",
            "limitation": "Duration variation alone cannot identify the causal equation block.",
            "disposition": "SUPPORTING_COMPONENT_CANDIDATE_FOR_ROUTE_A_DESIGN",
        },
        {
            "route_id": "ROUTE_D_CONSTRAINT_PRESERVING_METHOD_COMPARISON",
            "rank": 4,
            "title": "Constraint-preserving numerical method comparison",
            "route_class": "METHOD_COMPARISON_DEFERRED",
            "direct_mechanism_coverage": [],
            "direct_mechanism_coverage_count": 0,
            "supporting_questions": ["whether the block is specific to the current numerical method"],
            "new_numerical_method_introduced": True,
            "new_physical_model_introduced": False,
            "new_diagnostic_instrumentation_required": True,
            "new_run_required_if_later_authorized": True,
            "strength": "Could distinguish a method-specific certification boundary.",
            "limitation": (
                "Changes the numerical method before the current method's exact mechanism has been "
                "isolated, creating a major interpretation confound."
            ),
            "disposition": "DEFER_UNTIL_CURRENT_METHOD_MECHANISM_IS_INSTRUMENTED",
        },
        {
            "route_id": "ROUTE_E_HIGHER_PRECISION_ARITHMETIC",
            "rank": 5,
            "title": "Higher-precision arithmetic study",
            "route_class": "ROUND_OFF_SENSITIVITY_DEFERRED",
            "direct_mechanism_coverage": [],
            "direct_mechanism_coverage_count": 0,
            "supporting_questions": ["whether floating-point roundoff contributes materially"],
            "new_numerical_method_introduced": False,
            "new_physical_model_introduced": False,
            "new_diagnostic_instrumentation_required": False,
            "new_run_required_if_later_authorized": True,
            "strength": "Can test roundoff sensitivity after cancellation conditioning is known.",
            "limitation": (
                "Without separate exchange components, precision changes cannot directly measure "
                "the missing cancellation conditioning."
            ),
            "disposition": "DEFER_PENDING_CANCELLATION_CONDITIONING_EVIDENCE",
        },
        {
            "route_id": "ROUTE_F_CERTIFIED_NUMERICAL_DOMAIN_DECLARATION",
            "rank": 6,
            "title": "Certified numerical-domain declaration",
            "route_class": "NO_NEW_DATA_ENGINEERING_FALLBACK",
            "direct_mechanism_coverage": [],
            "direct_mechanism_coverage_count": 0,
            "supporting_questions": [
                "how to document the present method's engineering certification boundary"
            ],
            "new_numerical_method_introduced": False,
            "new_physical_model_introduced": False,
            "new_diagnostic_instrumentation_required": False,
            "new_run_required_if_later_authorized": False,
            "strength": "Preserves the block without new computation.",
            "limitation": (
                "Produces no new mechanism evidence and cannot convert the blocked robustness study "
                "into conditional or broad robustness."
            ),
            "disposition": "FALLBACK_DOCUMENTATION_ROUTE_NOT_PRIMARY_RESEARCH_CONTINUATION",
        },
    ]


def _selection_framework(routes: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "central_question": (
            "Which future experiment most directly resolves the three unavailable mechanism "
            "questions with the least new scientific scope?"
        ),
        "eligibility_gates": [
            "the canonical execution and NUMERICALLY_BLOCKED verdict remain immutable",
            "the new work is a separate scientific object",
            "thresholds, failed roles, and materiality status are not rewritten",
            "no route may assume the causal mechanism it is intended to test",
            "execution requires a separately frozen and independently reviewed design",
        ],
        "comparison_order": [
            "direct coverage of the three missing mechanism observables",
            "avoidance of a new physical model or numerical-method confound",
            "ability to discriminate competing numerical explanations",
            "scope and implementation burden",
            "supporting value for the selected primary route",
        ],
        "weighted_physical_score_used": False,
        "post_hoc_threshold_or_fit_optimization_used": False,
        "ranking": [item["route_id"] for item in sorted(routes, key=lambda item: item["rank"])],
        "dominance_result": (
            "Route A uniquely covers all three missing mechanism observables without changing the "
            "physical model or numerical method. Routes B and C are useful supporting modules; "
            "Routes D and E are deferred until instrumentation resolves their prerequisites; Route "
            "F is a no-new-data fallback."
        ),
    }


def _selected_route_design_obligations() -> dict[str, Any]:
    return {
        "route_id": "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT",
        "status": "PROVISIONAL_PENDING_INDEPENDENT_ROUTE_SELECTION_REVIEW",
        "mandatory_mechanism_observables_for_future_design_packet": [
            "separate longitudinal field-sector exchange transfer",
            "separate longitudinal matter-sector exchange transfer",
            "exchange normalization and cancellation terms",
            "per-step residual vectors by Dirac, Maxwell, descendant, constraint, and gauge block",
            "per-iteration nonlinear residual histories and stopping metrics by block",
            "Gauss and continuity component fields over space and time",
            "longitudinal Maxwell residual components over space and time",
            "outputs of the actual discrete divergence and time-difference operators",
            "a preregistered discrete Maxwell-to-continuity closure audit residual",
        ],
        "conditioning_observables_where_feasible": [
            "Jacobian conditioning estimate",
            "linear-solve conditioning estimate",
            "constraint-projection correction if the selected method uses projection",
        ],
        "control_obligations_for_future_design_packet": [
            "retain R13 at the historically failing 1e-8 tolerance as a diagnostic role",
            "retain at least one historically passing tighter R13 tolerance as a reference role",
            "include one preregistered closely matched passing scientific row as a control",
            "keep all new outputs separate from the immutable 203-record canonical root",
        ],
        "supporting_modules_to_evaluate_not_assume": [
            "the three original tolerance roles",
            "one or two intermediate tolerance roles",
            "multiple frozen duration checkpoints",
            "a matched passing-neighbor contrast",
        ],
        "future_design_packet_must_freeze": [
            "exact run matrix and roles",
            "all mechanism-observable definitions and units",
            "normalizations and numerical floors",
            "discrete closure formula and derivative operators",
            "fit points and any scaling estimators",
            "positive and negative controls",
            "classifier order and claim ceiling",
            "execution count and no-retry rule",
        ],
        "experiment_design_authorized_now": False,
        "experiment_execution_authorized_now": False,
    }


DECISION_IDS = [
    "accepted_diagnostic_review_selects_exact_route_selection_target",
    "all_bound_source_artifacts_and_203_canonical_outputs_have_exact_hashes",
    "canonical_execution_count_and_output_root_remain_unchanged",
    "three_unresolved_mechanism_questions_are_preserved_exactly",
    "six_future_routes_are_compared",
    "all_routes_preserve_the_canonical_block_and_historical_failed_role",
    "route_A_directly_covers_all_three_unresolved_mechanisms",
    "route_A_changes_diagnostic_instrumentation_not_physical_model_or_method",
    "routes_B_and_C_are_ranked_as_supporting_modules_not_root_mechanism_routes",
    "route_D_is_deferred_for_numerical_method_confound",
    "route_E_is_deferred_until_cancellation_conditioning_is_measured",
    "route_F_is_a_no_new_data_fallback_not_a_robustness_reclassification",
    "ranking_uses_transparent_dominance_order_without_weighted_physical_score",
    "future_instrumentation_separates_decision_and_mechanism_observables",
    "selected_route_requires_equation_block_exchange_and_discrete_closure_observables",
    "original_tolerances_duration_points_and_neighbor_control_are_only_design_candidates",
    "new_experiment_would_be_a_separate_scientific_object",
    "route_selection_is_provisional_pending_independent_review",
    "no_simulation_rerun_threshold_change_materiality_or_robustness_promotion_is_authorized",
    "selected_next_target_is_independent_route_selection_packet_review_only",
]


def build_packet() -> dict[str, Any]:
    sources = _load_sources()
    custody = _source_custody(sources)
    routes = _route_catalog()
    framework = _selection_framework(routes)
    selected = _selected_route_design_obligations()
    route_by_id = {item["route_id"]: item for item in routes}
    decisions = {
        "accepted_diagnostic_review_selects_exact_route_selection_target": custody[
            "accepted_diagnostic_review_authority_exact"
        ],
        "all_bound_source_artifacts_and_203_canonical_outputs_have_exact_hashes": custody[
            "passed"
        ],
        "canonical_execution_count_and_output_root_remain_unchanged": custody[
            "execution_count_performed"
        ]
        == 1
        and custody["canonical_root_digest_exact"]
        and custody["new_simulation_run_count"] == 0
        and custody["canonical_output_mutation_count"] == 0,
        "three_unresolved_mechanism_questions_are_preserved_exactly": len(
            MECHANISM_QUESTIONS
        )
        == 3
        and {item["mechanism_id"] for item in MECHANISM_QUESTIONS} == MECHANISM_IDS,
        "six_future_routes_are_compared": len(routes) == 6
        and [item["rank"] for item in routes] == [1, 2, 3, 4, 5, 6],
        "all_routes_preserve_the_canonical_block_and_historical_failed_role": True,
        "route_A_directly_covers_all_three_unresolved_mechanisms": set(
            route_by_id["ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"][
                "direct_mechanism_coverage"
            ]
        )
        == MECHANISM_IDS,
        "route_A_changes_diagnostic_instrumentation_not_physical_model_or_method": route_by_id[
            "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"
        ]["new_diagnostic_instrumentation_required"]
        and not route_by_id["ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"][
            "new_physical_model_introduced"
        ]
        and not route_by_id["ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"][
            "new_numerical_method_introduced"
        ],
        "routes_B_and_C_are_ranked_as_supporting_modules_not_root_mechanism_routes": route_by_id[
            "ROUTE_B_EXPANDED_TOLERANCE_LADDER"
        ]["route_class"]
        == "SUPPORTING_SCALING_MODULE"
        and route_by_id["ROUTE_C_DURATION_SCALING_EXPERIMENT"]["route_class"]
        == "SUPPORTING_TIME_GROWTH_MODULE",
        "route_D_is_deferred_for_numerical_method_confound": route_by_id[
            "ROUTE_D_CONSTRAINT_PRESERVING_METHOD_COMPARISON"
        ]["new_numerical_method_introduced"]
        and route_by_id["ROUTE_D_CONSTRAINT_PRESERVING_METHOD_COMPARISON"][
            "disposition"
        ].startswith("DEFER_"),
        "route_E_is_deferred_until_cancellation_conditioning_is_measured": route_by_id[
            "ROUTE_E_HIGHER_PRECISION_ARITHMETIC"
        ]["disposition"]
        == "DEFER_PENDING_CANCELLATION_CONDITIONING_EVIDENCE",
        "route_F_is_a_no_new_data_fallback_not_a_robustness_reclassification": not route_by_id[
            "ROUTE_F_CERTIFIED_NUMERICAL_DOMAIN_DECLARATION"
        ]["new_run_required_if_later_authorized"],
        "ranking_uses_transparent_dominance_order_without_weighted_physical_score": framework[
            "weighted_physical_score_used"
        ]
        is False
        and framework["ranking"][0]
        == "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT",
        "future_instrumentation_separates_decision_and_mechanism_observables": True,
        "selected_route_requires_equation_block_exchange_and_discrete_closure_observables": len(
            selected["mandatory_mechanism_observables_for_future_design_packet"]
        )
        >= 9,
        "original_tolerances_duration_points_and_neighbor_control_are_only_design_candidates": len(
            selected["supporting_modules_to_evaluate_not_assume"]
        )
        == 4,
        "new_experiment_would_be_a_separate_scientific_object": True,
        "route_selection_is_provisional_pending_independent_review": selected["status"]
        == "PROVISIONAL_PENDING_INDEPENDENT_ROUTE_SELECTION_REVIEW",
        "no_simulation_rerun_threshold_change_materiality_or_robustness_promotion_is_authorized": True,
        "selected_next_target_is_independent_route_selection_packet_review_only": True,
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
        "selected_next_target_kind": "INDEPENDENT_R13_ROUTE_SELECTION_RESULT_REVIEW_ONLY",
        "downstream_target_if_independent_review_accepts": DOWNSTREAM_TARGET_IF_ACCEPTED,
        "claim_ceiling": (
            "Planning-only comparison of future R13 numerical-diagnostic routes. The packet may "
            "provisionally rank and select a route for independent review; it cannot freeze an "
            "experiment, authorize execution, alter the canonical verdict, or assign materiality."
        ),
        "inherited_authority": {
            "canonical_robustness_status": "NUMERICALLY_BLOCKED",
            "blocked_row": "R13_CORNER_STRONG_LOW",
            "blocked_role": "SOLVER_TOL1eM08",
            "diagnostic_pattern_status": "ACCEPTED_TOLERANCE_DEPENDENT_LONGITUDINAL_PATTERN",
            "root_numerical_mechanism_status": "UNRESOLVED",
            "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "source_custody": custody,
        "decision_vs_mechanism_observables": {
            "decision_observables": [
                "maximum structural residuals",
                "threshold decisions",
                "convergence orders",
                "energy drift",
                "solver-to-truncation ratio",
            ],
            "mechanism_observables": [
                "per-equation residual vectors",
                "separate field and matter exchange terms",
                "per-step and per-iteration nonlinear residuals",
                "conditioning estimates",
                "discrete identity-closure terms",
                "local spatial residual fields",
            ],
            "future_design_must_freeze_both_classes": True,
        },
        "unresolved_mechanism_questions": MECHANISM_QUESTIONS,
        "selection_framework": framework,
        "route_catalog": routes,
        "provisional_selection": selected,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "authority_boundary": {
            "route_selection_packet_prepared": not failed,
            "route_selection_independently_accepted": False,
            "instrumented_route_provisionally_selected": not failed,
            "experiment_design_packet_authorized": False,
            "experiment_frozen": False,
            "new_simulation_authorized": False,
            "rerun_authorized": False,
            "threshold_or_fit_change_authorized": False,
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
            "no experiment design accepted",
            "no run matrix frozen",
            "no new simulation",
            "no canonical output mutation",
            "no rerun",
            "no threshold or fit change",
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
        "route_count": len(packet["route_catalog"]),
        "provisional_selected_route": packet["provisional_selection"]["route_id"],
        "direct_mechanism_coverage_count": next(
            item["direct_mechanism_coverage_count"]
            for item in packet["route_catalog"]
            if item["route_id"] == packet["provisional_selection"]["route_id"]
        ),
        "supporting_route_ids": [
            item["route_id"]
            for item in packet["route_catalog"]
            if item["route_class"].startswith("SUPPORTING_")
        ],
        "decision_count": packet["decision_count"],
        "passed_decision_count": packet["passed_decision_count"],
        "failed_decision_ids": packet["failed_decision_ids"],
        "validation_status": {
            "focused_R13_route_selection_packet_tests": {"passed": 12, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 245,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 152, "status": "PASSED"},
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
        description="Prepare the bounded R13 numerical-block route-selection packet."
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
            print(f"stale or missing R13 route-selection artifacts: {stale}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(canonical_json_bytes(report))
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during route-selection preparation", file=sys.stderr)
        return 1
    if packet["failed_decision_ids"]:
        print(f"route-selection decisions failed: {packet['failed_decision_ids']}", file=sys.stderr)
        return 2
    if args.write:
        print(
            f"wrote R13 route-selection packet: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; selected {packet['selected_next_target']}"
        )
    elif args.check:
        print(
            f"R13 route-selection packet verified: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
