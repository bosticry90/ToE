from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_report import (
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
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_"
    "20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
    "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_ACCEPTS_"
    "INCONCLUSIVE_RETEST_AND_AUTHORIZES_MODEL_REFINEMENT_OR_COUNTERMODEL_"
    "PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_retest_attempt_after_post_"
    "retest_refinement_conservation_retest_refinement_result_review_accepts_"
    "inconclusive_retest_and_authorizes_model_refinement_or_countermodel_"
    "packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_"
    "retest_refinement_conservation_retest_refinement"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_preparation_only"
)
SELECTED_REFINEMENT_TARGET = (
    "refine_post_retest_refined_weak_pairing_domain_or_scope_after_v3_"
    "inconclusive_retest_without_source_admissibility"
)
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_working_model_countermodel_packet_after_post_"
    "retest_refinement_conservation_retest_refinement"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_POST_"
        "RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_REVIEW_"
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
                "The accepted v3 retest result is inconclusive, so the single "
                "bounded next action is a model-refinement packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "This post-retest-refinement conservation-retest-refinement "
                "attempt result-review target is consumed here."
            ),
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "not_selected_no_failure_obstruction",
            "reason": (
                "The retest did not record an explicit failed-conservation "
                "obstruction requiring a countermodel packet."
            ),
        },
        {
            "target": (
                "execute_qft_gr_minimal_working_model_conservation_retest_"
                "attempt_after_post_retest_refinement_conservation_retest_"
                "refinement"
            ),
            "decision": "not_authorized_without_new_packet",
            "reason": "A new retest is not authorized without a new packet.",
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
                "The bounded v3 retest is inconclusive and points to further "
                "weak pairing-domain, regularity, source-definition, or scope "
                "refinement."
            ),
        },
        {
            "route": COUNTERMODEL_TARGET,
            "selected": False,
            "reason": (
                "Countermodel preparation is not selected because the retest "
                "did not fail or expose an explicit obstruction."
            ),
        },
    ]


def _refinement_target_rows() -> list[dict[str, Any]]:
    return [
        {
            "refinement_target": SELECTED_REFINEMENT_TARGET,
            "selected": True,
            "reason": (
                "The v3 weak pairing domain and regular context still do not "
                "decide zero versus nonzero weak divergence."
            ),
        },
        {
            "refinement_target": "construct_countermodel_for_failed_v3_retest",
            "selected": False,
            "reason": "No explicit failed conservation-retest obstruction was recorded.",
        },
        {
            "refinement_target": "promote_toy_candidate_to_admissible_source",
            "selected": False,
            "reason": "Source admissibility is not claimed or authorized.",
        },
        {
            "refinement_target": "derive_bianchi_compatible_semiclassical_coupling",
            "selected": False,
            "reason": (
                "Bianchi compatibility and the semiclassical Einstein equation "
                "remain outside this review."
            ),
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


def build_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    route_rows = _route_rows()
    refinement_target_rows = _refinement_target_rows()
    selected_refinement_targets = [
        row["refinement_target"] for row in refinement_target_rows if row["selected"]
    ]
    validation_policy = _validation_policy(attempt)

    acceptance_criteria = {
        "consumes_expected_v3_attempt": (
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
        "exactly_one_refinement_or_countermodel_route_selected": sum(
            1 for row in route_rows if row["selected"]
        )
        == 1,
        "exactly_one_refinement_target_selected": selected_refinement_targets
        == [SELECTED_REFINEMENT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_"
            "ATTEMPT_AFTER_POST_RETEST_REFINEMENT_CONSERVATION_RETEST_"
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
            "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_ATTEMPT_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_working_model_conservation_retest_attempt_after_"
            "post_retest_refinement_conservation_retest_refinement_result_"
            "review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review_accepted": (
            accepted
        ),
        "conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_consumed": (
            accepted
        ),
        "conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_executed": (
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
        "model_refinement_packet_authorized": accepted,
        "model_refinement_packet_prepared_by_review": False,
        "model_refinement_executed_by_review": False,
        "countermodel_packet_authorized": False,
        "countermodel_packet_prepared_by_review": False,
        "conservation_retest_rerun_authorized": False,
        "selected_refinement_or_countermodel_route": (
            NEXT_TARGET if accepted else "requires_remediation"
        ),
        "selected_refinement_or_countermodel_route_count": 1 if accepted else 0,
        "route_rows": route_rows,
        "selected_refinement_target": (
            SELECTED_REFINEMENT_TARGET if accepted else "requires_remediation"
        ),
        "selected_refinement_target_count": 1 if accepted else 0,
        "refinement_target_rows": refinement_target_rows,
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
            "PREPARE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_PACKET_AFTER_"
            "POST_RETEST_REFINEMENT_CONSERVATION_RETEST_REFINEMENT_ONLY_NO_"
            "RETEST_RERUN_NO_CONSERVATION_PROOF_WITNESS_SOURCE_ADMISSIBILITY_"
            "BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_"
            "VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the bounded v3 conservation-retest-"
            "refinement attempt as inconclusive and authorizes exactly one next "
            "bounded target: a model-refinement packet. It does not convert "
            "the inconclusive result into a pass or failure, does not rerun "
            "conservation, does not claim conservation, does not construct a "
            "conservation proof object, constructs no conservation witness, "
            "preserves no source admissibility, does not claim Bianchi "
            "compatibility, does not derive the semiclassical Einstein "
            "equation, does not close QFT-GR, does not validate empirically, "
            "does not authorize public submission, and does not promote the "
            "master action."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model v3 conservation-retest "
            "attempt result review after post-retest-refinement conservation-"
            "retest refinement."
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
    payload = write_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement_conservation_retest_refinement_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_retest_attempt_after_post_"
        "retest_refinement_conservation_retest_refinement_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
