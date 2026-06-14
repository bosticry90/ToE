from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    RETEST_CONDITION_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260613_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_ACCEPTS_"
    "PACKET_AND_AUTHORIZES_BOUNDED_CONSERVATION_RETEST_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_result_review_accepts_packet_"
    "and_authorizes_bounded_conservation_retest_attempt_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_"
    "post_retest_refinement_conservation_retest_refinement"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_"
    "refinement_conservation_retest_refinement_execution_only"
)
AUTHORIZED_CONSERVATION_RETEST_ATTEMPT_CLASSIFICATIONS = [
    (
        "qft_gr_minimal_working_model_conservation_retest_attempt_after_post_"
        "retest_refinement_conservation_retest_refinement_executed_pending_"
        "result_review"
    ),
    (
        "qft_gr_minimal_working_model_conservation_retest_after_post_retest_"
        "refinement_conservation_retest_refinement_passed_pending_result_review"
    ),
    (
        "qft_gr_minimal_working_model_conservation_retest_after_post_retest_"
        "refinement_conservation_retest_refinement_failed_requires_countermodel_"
        "or_scope_refinement"
    ),
    (
        "qft_gr_minimal_working_model_conservation_retest_after_post_retest_"
        "refinement_conservation_retest_refinement_inconclusive_requires_model_"
        "refinement"
    ),
]
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_POST_"
        "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_20260613_v0.json"
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


def _delta_changes(delta: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        row.get("component", ""): row
        for row in delta.get("changed_after_repeated_inconclusive_retests", [])
    }


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The v3 conservation-retest packet is accepted as a bounded "
                "protocol, so the next action may execute only that retest "
                "attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This v3 conservation-retest packet result-review target is "
                "consumed here."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The v3 toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The review authorizes a bounded retest attempt, not a proof.",
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
    inherited = packet.get("validation_policy", {})
    return {
        "checkpoint_type": "routine_conservation_retest_packet_result_review",
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
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "inherited_packet_validation_policy": inherited,
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


def build_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    refinement_delta = packet.get("newest_refinement_delta", {})
    delta_changes = _delta_changes(refinement_delta)
    retest_condition = packet.get("retest_conservation_condition", {})
    criteria = packet.get("pass_fail_inconclusive_criteria", {})
    pass_boundary = packet.get(
        "why_even_a_future_pass_does_not_imply_source_admissibility_or_qft_gr_closure",
        [],
    )
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(packet)
    packet_policy = packet.get("validation_policy", {})

    acceptance_criteria = {
        "consumes_expected_retest_packet": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_result_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_preparation_only_confirmed": packet.get("packet_preparation_only")
        is True
        and packet.get("retest_packet_prepared") is True
        and packet.get("conservation_retest_executed") is False,
        "newest_refinement_delta_defined": len(delta_changes) == 7
        and delta_changes.get("weak_pairing_domain", {}).get("component_id")
        == "toy_weak_pairing_domain_v3_candidate"
        and delta_changes.get("regularity_assumptions", {}).get("component_id")
        == "toy_regular_context_v3_candidate"
        and delta_changes.get("test_function_class", {}).get("component_id")
        == "toy_conservation_test_function_class_v2_candidate",
        "retest_condition_defined": retest_condition.get("condition_id")
        == RETEST_CONDITION_ID
        and retest_condition.get("weak_pairing_domain_id")
        == "toy_weak_pairing_domain_v3_candidate"
        and retest_condition.get("regularity_structure_id")
        == "toy_regular_context_v3_candidate"
        and retest_condition.get("test_function_class_id")
        == "toy_conservation_test_function_class_v2_candidate"
        and retest_condition.get("retest_executed") is False,
        "pass_fail_inconclusive_defined": set(criteria)
        == {"pass", "fail", "inconclusive"},
        "future_pass_boundary_preserved": len(pass_boundary) == 4
        and any("source admissibility" in row for row in pass_boundary)
        and any("Bianchi compatibility" in row for row in pass_boundary)
        and any("close QFT-GR" in row for row in pass_boundary),
        "toy_source_remains_candidate_only": packet.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility"
        and packet.get("toy_source_candidate_remains_candidate_only") is True,
        "no_retest_execution_by_review": packet.get("conservation_retest_executed")
        is False
        and packet.get("conservation_retest_result_claimed") is False
        and packet.get("conservation_retest_pass_claimed") is False,
        "no_source_admissibility_claim": packet.get("source_admissibility_claimed")
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": packet.get(
            "conservation_claimed"
        )
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
        "standing_validation_caveats_preserved": packet.get(
            "release_index_path_not_freshly_lean_validated"
        )
        is True
        and packet.get("aggregate_lean_not_run") is True
        and packet.get("aggregate_lean_health_claimed") is False
        and packet_policy.get("full_pytest_required") is False
        and packet_policy.get("full_governance_suite_required") is False
        and packet_policy.get("full_aggregate_lean_required") is False,
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
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_"
            "PACKET_AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_"
            "REFINEMENT_RESULT_REVIEW"
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
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_conservation_retest_packet_after_"
            "post_retest_refinement_conservation_retest_refinement_result_"
            "review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "packet_result_review_accepted": accepted,
        "retest_packet_result_review_accepted": accepted,
        "post_retest_refinement_conservation_retest_refinement_packet_result_review_accepted": (
            accepted
        ),
        "retest_packet_consumed": accepted,
        "post_retest_refinement_conservation_retest_refinement_packet_consumed": (
            accepted
        ),
        "retest_packet_preparation_only_confirmed": accepted,
        "bounded_conservation_retest_attempt_authorized": accepted,
        "bounded_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_authorized": (
            accepted
        ),
        "bounded_conservation_retest_attempt_executed_by_review": False,
        "conservation_retest_packet_result_reviewed": accepted,
        "conservation_retest_executed": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_retest_failure_claimed": False,
        "conservation_test_retried_as_proof": False,
        "newest_refinement_delta": refinement_delta,
        "retest_conservation_condition": retest_condition,
        "pass_fail_inconclusive_criteria": criteria,
        "why_even_a_future_pass_does_not_imply_source_admissibility_or_qft_gr_closure": (
            pass_boundary
        ),
        "conservation_retest_attempt_result_classifications": (
            AUTHORIZED_CONSERVATION_RETEST_ATTEMPT_CLASSIFICATIONS
        ),
        "conservation_retest_attempt_result_classification_count": len(
            AUTHORIZED_CONSERVATION_RETEST_ATTEMPT_CLASSIFICATIONS
        ),
        "toy_source_candidate_status": packet.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "future_pass_implies_source_admissibility": False,
        "future_pass_implies_qft_gr_closure": False,
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
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_packet_result_review_current_target_registry_gates": (
                "required_for_checkpoint"
            ),
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "bounded_lean_substitute_result_review_frontier": (
                "required_for_checkpoint"
            ),
            "git_diff_check": "required_for_checkpoint",
            "full_pytest": "not_required_for_checkpoint",
            "full_governance_suite": "not_required_for_checkpoint",
            "full_aggregate_lean": "not_required_for_checkpoint_preserved_caveat",
            "release_index_lean_path": "not_freshly_validated_preserved_caveat",
            "full_ci_parity": "not_required_for_checkpoint",
            "security_scan": "not_required_for_checkpoint",
        },
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded packet-result-review checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made. Timeouts remain validation caveats, not rerun instructions."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_"
            "AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_ONLY_"
            "NO_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_WITNESS_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_"
            "PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared v3 conservation-"
            "retest packet and authorizes one bounded conservation retest "
            "attempt. It does not execute the retest and preserves no source "
            "admissibility, no conservation claim, no conservation proof "
            "object, no conservation witness, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no QFT-GR closure, no empirical "
            "validation, no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model v3 conservation-retest "
            "packet result review."
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
    payload = write_qft_gr_minimal_working_model_conservation_retest_packet_after_post_retest_refinement_conservation_retest_refinement_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_retest_packet_after_post_"
        "retest_refinement_conservation_retest_refinement_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
