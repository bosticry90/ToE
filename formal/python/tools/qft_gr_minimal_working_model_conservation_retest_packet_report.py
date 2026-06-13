from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_REFINEMENT_ATTEMPT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REFINED_CANDIDATE_STATUS,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_20260613_v0"
PACKET_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_PROOF_OR_SOURCE_ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_retest_packet_prepared_pending_"
    "result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_working_model_conservation_retest_packet_result"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_conservation_retest_packet_result_review"
RETEST_CONDITION_ID = (
    "weak_distributional_covariant_conservation_for_refined_toy_candidate"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_20260613_v0.json"
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
                "The conservation-retest packet must be reviewed before any "
                "retest execution, conservation proof attempt, source "
                "admissibility claim, or closure routing is authorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This conservation-retest packet preparation target is consumed here.",
        },
        {
            "target": "execute_qft_gr_minimal_working_model_conservation_retest",
            "decision": "not_authorized_before_retest_packet_result_review",
            "reason": "This packet defines the retest only; it does not execute it.",
        },
        {
            "target": "retry_qft_gr_minimal_working_model_conservation_test_as_proof",
            "decision": "not_authorized",
            "reason": "A retest protocol is not a conservation proof.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The refined toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "No conservation proof is constructed by packet preparation.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by packet preparation.",
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
            "reason": "QFT-GR closure remains outside this packet.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _refinement_delta(review: dict[str, Any]) -> dict[str, Any]:
    weak_adjustment = review.get("weak_pairing_domain_adjustment", {})
    regularity_adjustment = review.get("regularity_structure_adjustment", {})
    return {
        "delta_id": "refined_toy_candidate_domain_and_regularity_delta_v1",
        "changed_after_first_conservation_test": [
            {
                "component": "weak_pairing_domain",
                "new_adjustment_id": review.get("weak_pairing_domain_adjustment_id"),
                "expected_adjustment_id": "toy_weak_pairing_domain_v1",
                "source_scope": weak_adjustment.get("scope"),
                "effect_on_retest": (
                    "Retest only pairings admitted by the refined weak "
                    "pairing-domain envelope."
                ),
                "source_admissibility_claimed": False,
                "conservation_claimed": False,
            },
            {
                "component": "regularity_structure",
                "new_adjustment_id": review.get("regularity_structure_adjustment_id"),
                "expected_adjustment_id": "toy_regular_context_v1",
                "source_scope": regularity_adjustment.get("scope"),
                "effect_on_retest": (
                    "Retest derivative, divergence, and limit/interchange "
                    "steps only where the refined regularity context admits them."
                ),
                "regularity_discharge_claimed": False,
                "source_admissibility_claimed": False,
            },
        ],
        "unchanged_boundaries": [
            "toy_source_candidate_status_remains_candidate_only",
            "fixed_background_only",
            "no_backreaction_or_semiclassical_einstein_equation",
            "no_Bianchi_compatibility",
            "no_source_admissibility",
            "no_QFT_GR_closure",
        ],
        "obstruction_accounting_preserved": review.get("obstruction_accounting", []),
    }


def _retest_condition(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "condition_id": RETEST_CONDITION_ID,
        "condition_being_retested": (
            "Weak distributional covariant conservation of the refined toy "
            "stress-energy-like candidate against the refined weak pairing "
            "domain and regularity context."
        ),
        "statement_template": (
            "For every retest-admitted compactly supported test vector field X, "
            "with pairings admitted by toy_weak_pairing_domain_v1 and derivative "
            "or limit operations admitted by toy_regular_context_v1, the weak "
            "pairing <div_g(T_refined), X> must vanish; otherwise record the "
            "first explicit obstruction."
        ),
        "refined_candidate_status": review.get("refined_candidate_status"),
        "weak_pairing_domain_id": review.get("weak_pairing_domain_adjustment_id"),
        "regularity_structure_id": review.get("regularity_structure_adjustment_id"),
        "fixed_background_only": True,
        "strong_pointwise_conservation_claimed": False,
        "global_conservation_claimed": False,
        "retest_executed": False,
    }


def _pass_fail_inconclusive_criteria() -> dict[str, list[str]]:
    return {
        "pass": [
            (
                "every retest-admitted weak pairing is defined under "
                "toy_weak_pairing_domain_v1"
            ),
            (
                "every derivative, divergence, and limit/interchange step used "
                "by the weak pairing is admitted by toy_regular_context_v1"
            ),
            (
                "every retest-admitted weak divergence pairing evaluates to "
                "zero without adding an unrecorded assumption"
            ),
            "no retest obstruction row is triggered by the retest matrix",
        ],
        "fail": [
            (
                "a retest-admitted weak divergence pairing is explicitly "
                "nonzero"
            ),
            (
                "a required pairing remains undefined inside "
                "toy_weak_pairing_domain_v1"
            ),
            (
                "a required derivative, divergence, regularization, or "
                "limit/interchange step remains blocked inside "
                "toy_regular_context_v1"
            ),
        ],
        "inconclusive": [
            (
                "the retest cannot decide zero versus nonzero under only the "
                "refined packet assumptions"
            ),
            (
                "the retest requires a stronger pairing domain, regularity "
                "structure, source-domain membership, or Bianchi compatibility "
                "than this packet may add"
            ),
            (
                "the weak retest remains separable from strong pointwise "
                "conservation only by preserving the candidate-only boundary"
            ),
        ],
    }


def _pass_boundary() -> list[str]:
    return [
        (
            "A pass would establish only that the refined toy candidate passes "
            "this packet's weak distributional retest on the fixed background."
        ),
        (
            "A pass would not establish full source-domain membership, "
            "stress-energy source admissibility, or physical-source status."
        ),
        (
            "A pass would not establish Bianchi compatibility or derive a "
            "semiclassical Einstein equation."
        ),
        (
            "A pass would not close QFT-GR, authorize empirical validation, "
            "authorize public submission, or promote the master action."
        ),
    ]


def build_qft_gr_minimal_working_model_conservation_retest_packet(
    *,
    refinement_attempt_result_review_path: Path = (
        DEFAULT_REFINEMENT_ATTEMPT_RESULT_REVIEW_PATH
    ),
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(refinement_attempt_result_review_path)
    candidate_next_targets = _candidate_next_targets()
    refinement_delta = _refinement_delta(review)
    retest_condition = _retest_condition(review)
    pass_fail_inconclusive_criteria = _pass_fail_inconclusive_criteria()
    pass_boundary = _pass_boundary()

    acceptance_criteria = {
        "consumes_expected_refinement_attempt_result_review": review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "refinement_attempt_result_review_outcome_expected": review.get(
            "outcome_id"
        )
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "refinement_attempt_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "refinement_attempt_result_review_selected_this_packet": review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "refined_candidate_accepted_for_retest_packet": review.get(
            "refined_candidate_accepted_for_retest_packet_preparation"
        )
        is True
        and review.get("refined_candidate_status") == REFINED_CANDIDATE_STATUS,
        "candidate_only_status_preserved": review.get(
            "candidate_only_status_preserved"
        )
        is True
        and review.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility",
        "weak_pairing_domain_change_defined": (
            review.get("weak_pairing_domain_adjustment_id")
            == "toy_weak_pairing_domain_v1"
        ),
        "regularity_structure_change_defined": (
            review.get("regularity_structure_adjustment_id")
            == "toy_regular_context_v1"
        ),
        "retest_condition_defined": retest_condition.get("condition_id")
        == RETEST_CONDITION_ID,
        "pass_fail_inconclusive_defined": set(pass_fail_inconclusive_criteria)
        == {"pass", "fail", "inconclusive"},
        "pass_boundary_records_no_source_or_closure": len(pass_boundary) == 4,
        "no_retest_execution": retest_condition.get("retest_executed") is False,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": review.get("conservation_claimed")
        is False
        and review.get("conservation_proved") is False
        and review.get("conservation_proof_object_constructed") is False
        and review.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": review.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and review.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": review.get("qft_gr_seam_closed") is False
        and review.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": review.get(
            "empirical_validation_claimed"
        )
        is False
        and review.get("public_submission_authorized") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET"
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "packet_prepared": accepted,
        "retest_packet_prepared": accepted,
        "packet_preparation_only": True,
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_conservation_retest_packet_requires_remediation",
        "packet_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_attempt_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_attempt_result_review_pointer": _ptr(
            refinement_attempt_result_review_path
        ),
        "consumed_refinement_attempt_result_review_schema_id": review.get("schema_id"),
        "consumed_refinement_attempt_result_review_outcome_id": review.get(
            "outcome_id"
        ),
        "consumed_refinement_attempt_result_review_classification": review.get(
            "result_review_classification"
        ),
        "refined_candidate_status": review.get("refined_candidate_status"),
        "toy_source_candidate_status": review.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "refinement_delta_after_first_conservation_test": refinement_delta,
        "retest_conservation_condition": retest_condition,
        "pass_fail_inconclusive_criteria": pass_fail_inconclusive_criteria,
        "why_even_a_pass_does_not_imply_source_admissibility_or_qft_gr_closure": (
            pass_boundary
        ),
        "conservation_retest_packet_result_reviewed": False,
        "conservation_retest_executed": False,
        "conservation_retest_result_claimed": False,
        "conservation_retest_pass_claimed": False,
        "conservation_test_retried_as_proof": False,
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
        "aggregate_lean_timeout_caveat_preserved": review.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": review.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_RETEST_PACKET_"
            "RESULT_ONLY_NO_RETEST_EXECUTION_SOURCE_ADMISSIBILITY_"
            "CONSERVATION_PROOF_WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_"
            "QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only a bounded conservation retest protocol "
            "for the refined toy source candidate. It defines what changed "
            "after refinement, the weak conservation condition to retest, "
            "pass/fail/inconclusive criteria, and why even a pass would not "
            "imply source admissibility or QFT-GR closure. It does not execute "
            "a retest and preserves no source admissibility, no conservation "
            "claim, no conservation proof object, no conservation witness, no "
            "Bianchi compatibility, no semiclassical Einstein equation, no "
            "QFT-GR closure, no empirical validation, no public submission, "
            "and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_retest_packet(
    *,
    refinement_attempt_result_review_path: Path = (
        DEFAULT_REFINEMENT_ATTEMPT_RESULT_REVIEW_PATH
    ),
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_retest_packet(
        refinement_attempt_result_review_path=refinement_attempt_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model conservation-retest packet."
        )
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_REFINEMENT_ATTEMPT_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_conservation_retest_packet(
        refinement_attempt_result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_retest_packet_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
