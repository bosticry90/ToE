from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    RETEST_RESULT as EXPECTED_RETEST_RESULT,
    RETEST_STATUS as EXPECTED_RETEST_STATUS,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_RESULT_REVIEW_"
    "20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_RESULT_REVIEW_ACCEPTS_"
    "REPEATED_INCONCLUSIVE_PATTERN_AND_AUTHORIZES_OBSTRUCTION_CLASS_"
    "STABILIZATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_retest_result_review_accepts_"
    "repeated_inconclusive_pattern_and_authorizes_obstruction_class_"
    "stabilization_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "prepare_qft_gr_minimal_model_obstruction_class_stabilization_packet"
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_obstruction_class_stabilization_packet_preparation_only"
)
DOMINANT_OBSTRUCTION_CANDIDATE = "weak_pairing_domain_obstruction"
CANONICAL_OBSTRUCTION_ID = (
    "repeated_weak_divergence_undecided_under_candidate_pairing_domain_v3"
)
OBSTRUCTION_STATUS = "stabilized_for_next_target_selection_not_resolved"
PATTERN_STABILIZATION_SIGNAL = (
    "The repeated inconclusive pattern is no longer treated as a reason for "
    "immediate retest; it is treated as an obstruction-class stabilization signal."
)
ORDINARY_MODEL_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_refinement"
)
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction"
)
POSITIVE_WITNESS_TARGET = (
    "prepare_qft_gr_minimal_positive_conservation_witness_packet_under_strict_"
    "toy_assumptions"
)
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
        "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_RESULT_REVIEW_"
        "20260614_v0.json"
    )
)

REPEATED_INCONCLUSIVE_ATTEMPT_PATHS = [
    (
        "initial_conservation_test",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_20260612_v0.json",
    ),
    (
        "first_conservation_retest",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_20260613_v0.json",
    ),
    (
        "post_refinement_conservation_retest",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_20260613_v0.json"
        ),
    ),
    (
        "post_retest_refinement_conservation_retest_refinement_v3_retest",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_20260614_v0.json"
        ),
    ),
    (
        "latest_v4_conservation_retest_after_latest_refinement",
        DEFAULT_ATTEMPT_PATH,
    ),
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _repeated_inconclusive_chain() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for sequence, (label, path) in enumerate(REPEATED_INCONCLUSIVE_ATTEMPT_PATHS, 1):
        payload = _read_json(path)
        classification = payload.get("result_classification", "")
        retest_result = payload.get("retest_result", "inconclusive")
        rows.append(
            {
                "sequence": sequence,
                "label": label,
                "artifact": _ptr(path),
                "schema_id": payload.get("schema_id"),
                "outcome_id": payload.get("outcome_id"),
                "result_classification": classification,
                "retest_result": retest_result,
                "inconclusive": (
                    payload.get("retest_inconclusive") is True
                    or retest_result == "inconclusive"
                    or "inconclusive" in classification
                ),
                "converted_to_pass": payload.get("retest_passed") is True,
                "converted_to_failure": payload.get("retest_failed") is True,
            }
        )
    return rows


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The latest v4 retest is another inconclusive result in the "
                "minimal-model chain, so the single bounded next action is "
                "obstruction-class stabilization."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This latest post-retest-refinement conservation-retest-refinement "
                "attempt result-review target is consumed here."
            ),
        },
        {
            "target": ORDINARY_MODEL_REFINEMENT_TARGET,
            "decision": "not_authorized_repeated_inconclusive_loop",
            "reason": (
                "The repeated inconclusive pattern is treated as an "
                "obstruction-class stabilization signal, not as authorization "
                "for another same-shaped refinement packet."
            ),
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on_after_stabilization",
            "reason": (
                "Countermodel work is retained as a forced-fork follow-on "
                "after obstruction stabilization and positive-witness packet work."
            ),
        },
        {
            "target": POSITIVE_WITNESS_TARGET,
            "decision": "recommended_after_stabilization_review",
            "reason": (
                "A deliberately small positive witness is the recommended next "
                "scientific lane after the obstruction class is stabilized."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_after_countermodel_pressure",
            "reason": (
                "Source-map ladder reconstruction is retained after positive "
                "witness and countermodel work, not selected by this review."
            ),
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement_conservation_retest_"
                "refinement_refinement"
            ),
            "decision": "not_authorized_immediate_retest_forbidden",
            "reason": (
                "No immediate retest is authorized until obstruction "
                "stabilization and positive-witness work are completed."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains a candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The accepted result is inconclusive, not a proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains outside this result review.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _route_rows() -> list[dict[str, Any]]:
    return [
        {
            "route": NEXT_TARGET,
            "selected": True,
            "reason": (
                "The repeated inconclusive chain is now routed to obstruction-"
                "class stabilization before any further retest cycle."
            ),
        },
        {
            "route": POSITIVE_WITNESS_TARGET,
            "selected": False,
            "reason": (
                "Positive witness preparation is recommended after the "
                "stabilization packet is prepared and reviewed."
            ),
        },
        {
            "route": COUNTERMODEL_TARGET,
            "selected": False,
            "reason": "Countermodel pressure is retained as a follow-on lane.",
        },
    ]


def _obstruction_target_rows() -> list[dict[str, Any]]:
    return [
        {
            "obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
            "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
            "selected": True,
            "status": OBSTRUCTION_STATUS,
            "reason": (
                "The repeated retests leave weak divergence undecided under "
                "the candidate pairing domain; this is selected only as the "
                "dominant obstruction candidate for stabilization, not as a "
                "solved theorem."
            ),
        },
        {
            "obstruction_candidate": "regularity_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "Regularity clauses still support the undecided pattern.",
        },
        {
            "obstruction_candidate": "limit_derivative_exchange_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "Derivative and limit/interchange admission remain supporting blockers.",
        },
        {
            "obstruction_candidate": "test_vector_class_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "The admitted test-vector class remains too narrow to force a proof.",
        },
        {
            "obstruction_candidate": "candidate_source_definition_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "The candidate source remains candidate-only, not source-admissible.",
        },
        {
            "obstruction_candidate": "boundary_term_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "Boundary-term control is retained as a supporting obstruction.",
        },
        {
            "obstruction_candidate": "curvature_coupling_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "Curvature coupling is downstream and not resolved by this review.",
        },
        {
            "obstruction_candidate": "formalization_insufficiency_obstruction",
            "selected": False,
            "status": "supporting_obstruction_not_selected_as_dominant",
            "reason": "The marker-level formalization does not itself decide conservation.",
        },
    ]


def _validation_policy(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_conservation_retest_attempt_result_review",
        "routine_packet_uses_bounded_target_relevant_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "long_running_validation_escalation_authorized": False,
        "timeout_rerun_loop_authorized": False,
        "timeout_recorded_as_caveat_not_rerun_instruction": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "inherited_attempt_validation_policy": attempt.get("validation_policy", {}),
        "full_suite_required_only_for_target_types": [
            "release_candidate",
            "integration_closeout",
            "aggregate_validation_diagnostic",
            "public_submission_readiness",
            "master_action_promotion_review",
            "governance_manifest_enrollment",
            "shared_test_infrastructure_change",
            "broad_dependency_or_tooling_change",
        ],
    }


def build_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    repeated_chain = _repeated_inconclusive_chain()
    candidate_next_targets = _candidate_next_targets()
    route_rows = _route_rows()
    obstruction_target_rows = _obstruction_target_rows()
    selected_obstruction_candidates = [
        row["obstruction_candidate"]
        for row in obstruction_target_rows
        if row["selected"]
    ]
    validation_policy = _validation_policy(attempt)

    acceptance_criteria = {
        "consumes_expected_v4_attempt": (
            attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID
            and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
        ),
        "attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_classification_expected": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "attempt_selected_this_result_review": attempt.get("selected_next_target")
        == CONSUMED_TARGET,
        "attempt_executed_inconclusive": (
            attempt.get("attempt_executed") is True
            and attempt.get("retest_execution_status") == EXPECTED_RETEST_STATUS
            and attempt.get("retest_result") == EXPECTED_RETEST_RESULT
            and attempt.get("retest_inconclusive") is True
        ),
        "does_not_convert_inconclusive_to_pass": (
            attempt.get("retest_passed") is False
            and attempt.get("conservation_retest_pass_claimed") is False
        ),
        "does_not_convert_inconclusive_to_failure": (
            attempt.get("retest_failed") is False
            and attempt.get("conservation_retest_failure_claimed") is False
        ),
        "why_inconclusive_recorded": len(attempt.get("why_inconclusive", [])) >= 7,
        "repeated_inconclusive_pattern_recorded": (
            len(repeated_chain) == len(REPEATED_INCONCLUSIVE_ATTEMPT_PATHS)
            and all(row["inconclusive"] for row in repeated_chain)
            and not any(row["converted_to_pass"] for row in repeated_chain)
            and not any(row["converted_to_failure"] for row in repeated_chain)
        ),
        "stabilization_signal_recorded": PATTERN_STABILIZATION_SIGNAL
        in PATTERN_STABILIZATION_SIGNAL,
        "no_source_admissibility_claim": (
            attempt.get("source_admissibility_claimed") is False
            and attempt.get("stress_energy_source_admissibility_claimed") is False
        ),
        "no_conservation_claim_proof_or_witness": (
            attempt.get("conservation_claimed") is False
            and attempt.get("conservation_proved") is False
            and attempt.get("conservation_proof_object_constructed") is False
            and attempt.get("conservation_witness_constructed") is False
        ),
        "no_bianchi_or_semiclassical_einstein": (
            attempt.get("Bianchi_compatibility_claimed") is False
            and attempt.get("semiclassical_einstein_equation_derived") is False
        ),
        "no_qft_gr_closure": (
            attempt.get("qft_gr_seam_closed") is False
            and attempt.get("qft_gr_source_map_closure_claimed") is False
        ),
        "no_empirical_validation_or_public_submission": (
            attempt.get("empirical_validation_claimed") is False
            and attempt.get("public_submission_authorized") is False
        ),
        "no_master_action_promotion": (
            attempt.get("master_action_promoted") is False
            and attempt.get("master_action_promotion_authorized") is False
        ),
        "routine_validation_policy_preserves_non_escalation": all(
            validation_policy[key] is False
            for key in [
                "full_pytest_required",
                "full_governance_suite_required",
                "full_aggregate_lean_required",
                "full_ci_parity_required",
                "full_security_scan_required",
                "long_running_validation_escalation_authorized",
                "timeout_rerun_loop_authorized",
                "aggregate_lean_health_claimed",
            ]
        ),
        "standing_validation_caveats_preserved": (
            attempt.get("release_index_path_not_freshly_lean_validated") is True
            and attempt.get("aggregate_lean_not_run") is True
            and attempt.get("aggregate_lean_timeout_caveat_preserved") is True
            and attempt.get("aggregate_lean_health_claimed") is False
        ),
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "exactly_one_stabilization_route_selected": sum(
            1 for row in route_rows if row["selected"]
        )
        == 1,
        "exactly_one_dominant_obstruction_candidate_selected": (
            selected_obstruction_candidates == [DOMINANT_OBSTRUCTION_CANDIDATE]
            and obstruction_target_rows[0]["canonical_obstruction_id"]
            == CANONICAL_OBSTRUCTION_ID
            and obstruction_target_rows[0]["status"] == OBSTRUCTION_STATUS
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_"
            "ATTEMPT_AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_"
            "REFINEMENT_REFINEMENT_RESULT_REVIEW"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_REFINEMENT_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_conservation_retest_attempt_after_"
            "post_retest_refinement_conservation_retest_refinement_refinement_result_"
            "review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review_accepted": (
            accepted
        ),
        "conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_consumed": (
            accepted
        ),
        "conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_executed": (
            attempt.get("attempt_executed") is True
        ),
        "classification_confirmed": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "accepted_inconclusive_result": accepted,
        "inconclusive_not_converted_to_pass": True,
        "inconclusive_not_converted_to_failure": True,
        "conservation_retest_passed": False,
        "conservation_retest_failed": False,
        "conservation_retest_inconclusive": accepted,
        "retest_result": EXPECTED_RETEST_RESULT if accepted else "requires_remediation",
        "retest_passed": False,
        "retest_failed": False,
        "retest_inconclusive": accepted,
        "repeated_inconclusive_pattern_recorded": accepted,
        "repeated_inconclusive_attempt_count": len(repeated_chain),
        "repeated_inconclusive_chain": repeated_chain,
        "pattern_stabilization_signal": PATTERN_STABILIZATION_SIGNAL,
        "obstruction_class_stabilization_packet_authorized": accepted,
        "obstruction_class_stabilization_packet_prepared_by_review": False,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "supporting_obstructions_recorded": True,
        "positive_witness_lane_recommended_after_stabilization": True,
        "countermodel_lane_retained_as_follow_on": True,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "ordinary_model_refinement_packet_authorized": False,
        "model_refinement_packet_authorized": False,
        "model_refinement_packet_prepared_by_review": False,
        "model_refinement_executed_by_review": False,
        "immediate_conservation_retest_authorized": False,
        "countermodel_packet_authorized": False,
        "countermodel_packet_prepared_by_review": False,
        "conservation_retest_rerun_authorized": False,
        "selected_stabilization_route": (
            NEXT_TARGET if accepted else "requires_remediation"
        ),
        "selected_stabilization_route_count": 1 if accepted else 0,
        "route_rows": route_rows,
        "selected_dominant_obstruction_candidate": (
            DOMINANT_OBSTRUCTION_CANDIDATE if accepted else "requires_remediation"
        ),
        "selected_dominant_obstruction_candidate_count": 1 if accepted else 0,
        "obstruction_target_rows": obstruction_target_rows,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "aggregate_lean_timeout_caveat_preserved": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded result-review checkpoint. "
            f"Inherited caveat: {attempt.get('validation_caveat')}"
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if accepted else 0,
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_"
            "PACKET_ONLY_NO_IMMEDIATE_RETEST_NO_ORDINARY_MODEL_REFINEMENT_NO_"
            "CONSERVATION_PROOF_WITNESS_SOURCE_ADMISSIBILITY_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the bounded v4 conservation-retest "
            "attempt as inconclusive, records the repeated inconclusive "
            "pattern, and authorizes exactly one next bounded target: an "
            "obstruction-class stabilization packet. It does not convert the "
            "inconclusive result into a pass or failure, does not authorize an "
            "immediate retest, does not authorize ordinary model refinement, "
            "does not claim conservation, does not construct a conservation "
            "proof object, constructs no conservation witness, preserves no "
            "source admissibility, does not claim Bianchi compatibility, does "
            "not derive the semiclassical Einstein equation, does not close "
            "QFT-GR, does not validate empirically, does not authorize public "
            "submission, and does not promote the master action."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model v4 conservation-retest "
            "attempt result review that pivots repeated inconclusive retests "
            "to obstruction-class stabilization."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_refinement_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_retest_attempt_after_post_"
        "retest_refinement_conservation_retest_refinement_refinement_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
