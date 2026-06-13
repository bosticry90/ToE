from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    REFINEMENT_OBJECTIVE,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_REVIEW_20260613_v0"
REVIEW_ID = "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_REVIEW_ACCEPTS_"
    "REFINED_CANDIDATE_AND_AUTHORIZES_BOUNDED_CONSERVATION_RETEST_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_attempt_result_review_accepts_"
    "refined_candidate_and_authorizes_bounded_conservation_retest_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "prepare_qft_gr_minimal_working_model_conservation_retest_packet"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_conservation_retest_packet_preparation_only"
REFINED_CANDIDATE_STATUS = (
    "candidate_only_refined_for_bounded_conservation_retest_packet_preparation"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_REVIEW_20260613_v0.json"
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
                "The refinement attempt is accepted as a candidate-only domain "
                "and regularity adjustment, so the next bounded action may "
                "prepare only a conservation-retest packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This refinement-attempt result-review target is consumed here.",
        },
        {
            "target": "execute_qft_gr_minimal_working_model_conservation_retest",
            "decision": "not_authorized_before_retest_packet_preparation_and_review",
            "reason": "A retest packet must be prepared and reviewed before execution.",
        },
        {
            "target": "retry_qft_gr_minimal_working_model_conservation_test_as_proof",
            "decision": "not_authorized",
            "reason": "The review authorizes a packet only, not a proof or retest.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "No conservation proof is constructed or authorized.",
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


def _attempt_nonclaim_keys() -> list[str]:
    return [
        "toy_source_promoted_to_admissible_source",
        "conservation_test_retried",
        "conservation_test_executed_by_attempt",
        "conservation_test_result_claimed",
        "conservation_test_pass_claimed",
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
        "conservation_claimed",
        "conservation_proved",
        "conservation_proof_object_constructed",
        "conservation_witness_constructed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_claimed",
        "empirical_validation_claimed",
        "scientific_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "release_assembly_authorized",
        "release_packet_assembled",
        "public_submission_authorized",
        "publication_authorized",
    ]


def build_qft_gr_minimal_working_model_refinement_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    weak_adjustment = attempt.get("weak_pairing_domain_adjustment", {})
    regularity_adjustment = attempt.get("regularity_structure_adjustment", {})
    obstruction_accounting = attempt.get("obstruction_accounting", [])

    acceptance_criteria = {
        "consumes_expected_refinement_attempt": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID
        and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID,
        "attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_classification_expected": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "attempt_selected_this_result_review": attempt.get("selected_next_target")
        == CONSUMED_TARGET,
        "attempt_executed": attempt.get("attempt_executed") is True
        and attempt.get("bounded_refinement_attempt_executed") is True
        and attempt.get("refinement_attempt_executed") is True,
        "refinement_objective_confirmed": attempt.get("refinement_objective")
        == REFINEMENT_OBJECTIVE
        and attempt.get("selected_refinement_target") == REFINEMENT_OBJECTIVE,
        "candidate_only_status_preserved": attempt.get("candidate_only_status_preserved")
        is True
        and attempt.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility"
        and attempt.get("toy_source_candidate_remains_candidate_only") is True,
        "weak_pairing_domain_adjustment_only": attempt.get(
            "weak_pairing_domain_adjusted"
        )
        is True
        and weak_adjustment.get("adjustment_id") == "toy_weak_pairing_domain_v1"
        and weak_adjustment.get("scope") == "weak_pairing_domain"
        and weak_adjustment.get("source_admissibility_claimed") is False
        and weak_adjustment.get("conservation_claimed") is False,
        "regularity_structure_adjustment_only": attempt.get(
            "regularity_structure_adjusted"
        )
        is True
        and regularity_adjustment.get("adjustment_id") == "toy_regular_context_v1"
        and regularity_adjustment.get("scope") == "regularity"
        and regularity_adjustment.get("regularity_discharge_claimed") is False
        and regularity_adjustment.get("source_admissibility_claimed") is False,
        "obstruction_accounting_preserved_without_promotion": len(
            obstruction_accounting
        )
        == 4
        and all(
            row.get("source_admissibility_claimed") is False
            and row.get("conservation_claimed") is False
            for row in obstruction_accounting
        ),
        "no_conservation_retry_or_retest_execution": attempt.get(
            "conservation_test_retried"
        )
        is False
        and attempt.get("conservation_test_executed_by_attempt") is False
        and attempt.get("conservation_test_result_claimed") is False
        and attempt.get("conservation_test_pass_claimed") is False,
        "no_source_admissibility_claim": attempt.get("source_admissibility_claimed")
        is False
        and attempt.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": attempt.get(
            "conservation_claimed"
        )
        is False
        and attempt.get("conservation_proved") is False
        and attempt.get("conservation_proof_object_constructed") is False
        and attempt.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": attempt.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and attempt.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": attempt.get("qft_gr_seam_closed") is False
        and attempt.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": attempt.get(
            "empirical_validation_claimed"
        )
        is False
        and attempt.get("public_submission_authorized") is False,
        "no_master_action_promotion": attempt.get("master_action_promoted") is False
        and attempt.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_REVIEW"
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
        else "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_refinement_attempt_result_review_requires_remediation",
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_attempt": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "refinement_attempt_result_review_accepted": accepted,
        "refinement_attempt_consumed": accepted,
        "refinement_attempt_executed": attempt.get("refinement_attempt_executed")
        is True,
        "bounded_refinement_attempt_executed": attempt.get(
            "bounded_refinement_attempt_executed"
        )
        is True,
        "classification_confirmed": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "refined_candidate_accepted": accepted,
        "refined_candidate_accepted_for_retest_packet_preparation": accepted,
        "refined_candidate_status": REFINED_CANDIDATE_STATUS
        if accepted
        else "requires_remediation",
        "candidate_only_status_preserved": accepted,
        "toy_source_candidate_status": "candidate_only_not_source_admissibility",
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "refinement_objective": REFINEMENT_OBJECTIVE
        if accepted
        else "requires_remediation",
        "selected_refinement_target": REFINEMENT_OBJECTIVE
        if accepted
        else "requires_remediation",
        "selected_refinement_target_count": 1 if accepted else 0,
        "weak_pairing_domain_adjustment_accepted": accepted,
        "regularity_structure_adjustment_accepted": accepted,
        "weak_pairing_domain_adjustment_id": weak_adjustment.get("adjustment_id"),
        "regularity_structure_adjustment_id": regularity_adjustment.get(
            "adjustment_id"
        ),
        "weak_pairing_domain_adjustment": weak_adjustment,
        "regularity_structure_adjustment": regularity_adjustment,
        "obstruction_accounting": obstruction_accounting,
        "conservation_retest_packet_authorized": accepted,
        "conservation_retest_packet_prepared_by_review": False,
        "conservation_retest_executed_by_review": False,
        "conservation_retest_pass_claimed_by_review": False,
        "conservation_test_retried": False,
        "conservation_test_executed_by_review": False,
        "conservation_test_result_claimed": False,
        "conservation_test_pass_claimed": False,
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
        "attempt_nonclaim_keys_checked": _attempt_nonclaim_keys(),
        "aggregate_lean_timeout_caveat_preserved": attempt.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": attempt.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if accepted else 0,
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_"
            "ONLY_NO_RETEST_EXECUTION_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_"
            "WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_"
            "EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the refined candidate weak pairing "
            "domain and regularity structure for bounded conservation-retest "
            "packet preparation. It does not execute a conservation retest, "
            "does not retry conservation as proof, does not claim source "
            "admissibility, does not claim conservation, constructs no "
            "conservation proof object or conservation witness, claims no "
            "Bianchi compatibility, derives no semiclassical Einstein equation, "
            "closes no QFT-GR seam, validates nothing empirically, authorizes "
            "no public submission, and promotes no master action. Boundary "
            "shorthand: no source admissibility, no conservation proof object, "
            "no conservation witness, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no QFT-GR closure, and no "
            "public submission."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_refinement_attempt_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model refinement-attempt "
            "result review."
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
    payload = write_qft_gr_minimal_working_model_refinement_attempt_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
