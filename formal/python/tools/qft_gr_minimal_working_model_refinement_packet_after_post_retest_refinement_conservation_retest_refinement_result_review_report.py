from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_CLASS,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    REFINEMENT_OBJECTIVE,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
    "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_ACCEPTS_"
    "PACKET_AND_AUTHORIZES_BOUNDED_REFINEMENT_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_result_review_accepts_packet_"
    "and_authorizes_bounded_refinement_attempt_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "execute_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
    "refinement_conservation_retest_refinement"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_refinement_attempt_after_post_retest_"
    "refinement_conservation_retest_refinement_execution_only"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
        "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_"
        "20260614_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The v3-inconclusive refinement packet is accepted as a "
                "preparation artifact, so the only authorized next action is "
                "the scoped bounded refinement attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This refinement-packet result-review target is consumed here.",
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement_conservation_retest_"
                "refinement"
            ),
            "decision": "not_authorized_before_new_refinement_attempt",
            "reason": "The review authorizes refinement execution, not another retest.",
        },
        {
            "target": (
                "prepare_qft_gr_minimal_working_model_countermodel_packet_after_"
                "post_retest_refinement_conservation_retest_refinement"
            ),
            "decision": "not_selected_no_failed_retest_obstruction",
            "reason": (
                "The packet records an inconclusive v3 retest, not an explicit "
                "failed-retest countermodel obstruction."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The accepted packet contains refinement dimensions, not a proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized by review.",
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


def _validation_policy(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_packet_result_review_after_v3_inconclusive_retest",
        "routine_packet_review_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_packet_validation_policy": packet.get("validation_policy", {}),
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


def build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    refinement_dimensions = packet.get("refinement_dimensions", [])
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(packet)
    refinement_scopes = {row.get("scope") for row in refinement_dimensions}

    acceptance_criteria = {
        "consumes_expected_refinement_packet": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_result_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_preparation_only_confirmed": packet.get("packet_preparation_only")
        is True
        and packet.get("model_refinement_packet_preparation_only") is True
        and packet.get("model_refinement_executed") is False
        and packet.get("refinement_attempt_executed") is False,
        "v3_repeated_inconclusive_signal_confirmed": packet.get(
            "repeated_inconclusive_signal_count"
        )
        == 3,
        "obstruction_class_confirmed": packet.get("obstruction_class")
        == OBSTRUCTION_CLASS,
        "candidate_only_status_preserved": packet.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility"
        and packet.get("toy_source_candidate_remains_candidate_only") is True,
        "selected_refinement_objective_confirmed": packet.get(
            "refinement_objective"
        )
        == REFINEMENT_OBJECTIVE
        and packet.get("selected_refinement_target") == REFINEMENT_OBJECTIVE,
        "v4_refinement_dimensions_confirmed": refinement_scopes
        >= {
            "weak_pairing_domain",
            "regularity_assumptions",
            "test_function_class",
            "candidate_source_definition",
            "scope_restriction",
            "obstruction_accounting",
            "validation_boundary",
        },
        "v4_candidate_revisions_recorded": (
            packet.get("proposed_weak_pairing_domain_revision")
            == "toy_weak_pairing_domain_v4_candidate"
            and packet.get("proposed_regular_context_revision")
            == "toy_regular_context_v4_candidate"
            and packet.get("proposed_test_function_class_revision")
            == "toy_conservation_test_function_class_v3_candidate"
            and packet.get("proposed_candidate_source_definition_revision")
            == "toy_source_candidate_definition_v4_candidate"
        ),
        "review_gate_requirements_recorded": len(
            packet.get("review_gate_requirements", [])
        )
        >= 13,
        "no_conservation_rerun_or_retest_execution": packet.get(
            "conservation_retest_retried"
        )
        is False
        and packet.get("conservation_retest_executed_by_packet") is False
        and packet.get("conservation_retest_result_claimed") is False,
        "no_countermodel_packet_prepared_or_authorized": packet.get(
            "countermodel_packet_authorized"
        )
        is False
        and packet.get("countermodel_packet_prepared") is False,
        "no_source_admissibility_claim": packet.get("source_admissibility_claimed")
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": packet.get("conservation_claimed")
        is False
        and packet.get("conservation_proved") is False
        and packet.get("conservation_proof_object_constructed") is False
        and packet.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": packet.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and packet.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": packet.get("qft_gr_seam_closed") is False
        and packet.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("public_submission_authorized") is False,
        "no_master_action_promotion": packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "standing_lean_caveats_preserved": packet.get(
            "release_index_path_not_freshly_lean_validated"
        )
        is True
        and packet.get("aggregate_lean_not_run") is True
        and packet.get("aggregate_lean_health_claimed") is False,
        "long_running_validation_policy_preserves_non_escalation": all(
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
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW"
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
            "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_POST_RETEST_"
            "REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_REQUIRES_"
            "REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
            "refinement_conservation_retest_refinement_result_review_requires_"
            "remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_pointer": (
            _ptr(packet_path)
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "refinement_packet_result_review_accepted": accepted,
        "packet_preparation_only_confirmed": accepted,
        "v3_repeated_inconclusive_signal_confirmed": accepted,
        "obstruction_class": OBSTRUCTION_CLASS,
        "obstruction_class_confirmed": accepted,
        "candidate_only_status_preserved": accepted,
        "toy_source_candidate_status": packet.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": accepted,
        "toy_source_promoted_to_admissible_source": False,
        "bounded_refinement_attempt_authorized": accepted,
        "refinement_attempt_authorized": accepted,
        "bounded_refinement_attempt_executed_by_review": False,
        "bounded_refinement_attempt_executed": False,
        "refinement_attempt_executed": False,
        "model_refinement_packet_prepared": accepted,
        "model_refinement_executed_by_review": False,
        "refinement_objective": REFINEMENT_OBJECTIVE
        if accepted
        else "requires_remediation",
        "selected_refinement_target": REFINEMENT_OBJECTIVE
        if accepted
        else "requires_remediation",
        "selected_refinement_target_count": 1 if accepted else 0,
        "refinement_focus": packet.get("refinement_focus"),
        "current_weak_pairing_domain_id": packet.get("current_weak_pairing_domain_id"),
        "proposed_weak_pairing_domain_revision": packet.get(
            "proposed_weak_pairing_domain_revision"
        ),
        "current_regular_context_id": packet.get("current_regular_context_id"),
        "proposed_regular_context_revision": packet.get(
            "proposed_regular_context_revision"
        ),
        "current_test_function_class_id": packet.get("current_test_function_class_id"),
        "proposed_test_function_class_revision": packet.get(
            "proposed_test_function_class_revision"
        ),
        "current_candidate_source_definition_id": packet.get(
            "current_candidate_source_definition_id"
        ),
        "proposed_candidate_source_definition_revision": packet.get(
            "proposed_candidate_source_definition_revision"
        ),
        "refinement_dimensions": refinement_dimensions,
        "identified_refinement_scopes": sorted(refinement_scopes),
        "review_gate_requirements": packet.get("review_gate_requirements", []),
        "conservation_retest_retried": False,
        "conservation_retest_executed_by_review": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_retest_failure_claimed": False,
        "countermodel_packet_authorized": False,
        "countermodel_packet_prepared": False,
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
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "validation_caveat": (
            "Bounded routine validation applies. The release-index path is "
            "not freshly Lean-validated, aggregate Lean is not run, and no "
            "aggregate Lean health claim is made. Timeouts are recorded as "
            "validation caveats, not retry instructions."
        ),
        "validation_policy": validation_policy,
        "validation_non_escalation_boundary": (
            "Routine packet/review checkpoints use bounded target-relevant "
            "validation only. Full-suite validation is not retried or escalated "
            "unless the checkpoint type requires it."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_ONLY_NO_"
            "REFINEMENT_EXECUTION_BY_REVIEW_CONSERVATION_RERUN_COUNTERMODEL_"
            "PACKET_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_WITNESS_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_"
            "PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared v3-inconclusive "
            "refinement packet and authorizes one bounded refinement attempt. "
            "It does not execute the refinement attempt, rerun conservation, "
            "prepare a countermodel packet, claim source admissibility, claim "
            "conservation, construct a conservation proof object or witness, "
            "claim Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, authorize public "
            "submission, or promote the master action. Boundary shorthand: no "
            "source admissibility, no conservation proof object, no conservation "
            "witness, no Bianchi compatibility, no semiclassical Einstein "
            "equation, no QFT-GR closure, and no public submission."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model v3-inconclusive "
            "refinement-packet result review."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_refinement_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
        "refinement_conservation_retest_refinement_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
