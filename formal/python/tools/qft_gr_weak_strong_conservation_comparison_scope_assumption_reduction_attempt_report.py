from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_report import (
    BLOCKER,
    COMPARISON_SCOPE_BOUNDARIES,
    DEFAULT_CAPTURED_AT_UTC,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_ROW_ID,
    SELECTED_ROW_OBJECT,
    STRONG_CONSERVATION_SCOPE,
    WEAK_CONSERVATION_SCOPE,
)
from formal.python.tools.qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review_report import (
    AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
    DEFAULT_OUT as DEFAULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_EXECUTION_TARGET,
    OUTCOME_ID as EXPECTED_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_REVIEW_ID,
    SCHEMA_ID as EXPECTED_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_"
    "ATTEMPT_20260609_v0"
)
ATTEMPT_ID = (
    "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_"
    "ATTEMPT_v0"
)
OUTCOME_ID = (
    "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_"
    "ATTEMPT_EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
CONSUMED_TARGET = EXPECTED_EXECUTION_TARGET
NEXT_TARGET = (
    "review_qft_gr_weak_strong_conservation_comparison_scope_assumption_"
    "reduction_attempt_result"
)
RESULT_CLASSIFICATION = (
    "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduced_pending_"
    "result_review"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_CONTRACT_ID = (
    "MR-ASSUMP-002-weak_strong_conservation_comparison_scope_contract_v0"
)
BOUNDED_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_CONTRACT_STATUS = (
    "bounded_repo_local_weak_strong_conservation_comparison_scope_contract_"
    "pending_result_review_not_conservation_discharge"
)
REQUIRED_FUTURE_PROOF_OBJECT = "weak_strong_conservation_comparison_regular_scope"
CANDIDATE_REDUCTION_ROUTE = (
    "record weak/strong scope-comparison regularity as a bounded contract for "
    "future conservation proof-object work, without claiming weak or strong "
    "conservation."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_"
        "ATTEMPT_20260609_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded MR-ASSUMP-002 attempt must be result-reviewed before "
                "any downstream mathematical-regularity row or conservation work."
            ),
        },
        {
            "target": "execute_qft_gr_distributional_pairing_regular_domain_assumption_reduction_attempt",
            "decision": "not_authorized_current_row",
            "reason": "MR-ASSUMP-003 remains downstream of MR-ASSUMP-002 result review.",
        },
        {
            "target": "execute_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt",
            "decision": "not_authorized_current_row",
            "reason": "MR-ASSUMP-004 remains downstream of MR-ASSUMP-002 result review.",
        },
        {
            "target": "prove_qft_gr_weak_conservation",
            "decision": "not_authorized",
            "reason": "This bounded attempt does not prove weak conservation.",
        },
        {
            "target": "prove_qft_gr_strong_conservation",
            "decision": "not_authorized",
            "reason": "This bounded attempt does not prove strong conservation.",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "No conservation proof object is constructed or authorized here.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized here.",
        },
        {
            "target": "claim_qft_gr_state_admissibility",
            "decision": "not_authorized",
            "reason": "MR-ASSUMP-002 attempt does not imply state admissibility.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "MR-ASSUMP-002 attempt does not imply source admissibility.",
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
            "reason": "No bounded assumption-reduction attempt closes QFT-GR.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission remain outside this checkpoint.",
        },
    ]


def build_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    candidate_next_targets = _candidate_next_targets()
    classification_rows = [
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[0],
            "selected": True,
            "meaning": (
                "MR-ASSUMP-002 has been reduced to a bounded repo-local weak/strong "
                "comparison-scope contract pending result review, without proving "
                "weak or strong conservation."
            ),
        },
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[1],
            "selected": False,
            "meaning": (
                "The attempt found an obstruction requiring refinement before "
                "the weak/strong comparison scope could be reduced."
            ),
        },
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[2],
            "selected": False,
            "meaning": (
                "The attempt could not determine reduction status without "
                "further assumption reduction."
            ),
        },
    ]
    reduction_contract = {
        "contract_id": WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_CONTRACT_ID,
        "assumption_id": SELECTED_ROW_ID,
        "assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "regularity_condition": SELECTED_ROW_OBJECT,
        "weak_scope": WEAK_CONSERVATION_SCOPE,
        "strong_scope": STRONG_CONSERVATION_SCOPE,
        "comparison_scope_boundaries": COMPARISON_SCOPE_BOUNDARIES,
        "contract_status": BOUNDED_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_CONTRACT_STATUS,
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "available_repo_evidence": [
            EXPECTED_REVIEW_ID,
            review.get("consumed_packet_outcome_id", ""),
            review.get("consumed_packet_classification", ""),
        ],
        "claim_ceiling": (
            "weak_strong_comparison_scope_contract_pending_result_review_only_"
            "no_weak_or_strong_conservation_proof_no_conservation_proof_object_"
            "no_conservation_witness_no_state_or_source_admissibility_no_bianchi_"
            "no_qft_gr_seam_closure"
        ),
    }
    execution_findings = [
        "The attempt consumes the accepted MR-ASSUMP-002 packet result review and executes only MR-ASSUMP-002.",
        "The bounded contract pins weak/strong scope-comparison regularity for future proof-object work.",
        "The reduction remains pending result review and does not prove weak or strong conservation.",
        "The attempt constructs no conservation proof object or conservation witness and leaves insufficient_assumptions_for_conservation active.",
    ]

    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("review_id") == EXPECTED_REVIEW_ID,
        "review_schema_expected": review.get("schema_id") == EXPECTED_REVIEW_SCHEMA_ID,
        "review_outcome_expected": review.get("outcome_id") == EXPECTED_REVIEW_OUTCOME,
        "review_classification_expected": review.get("result_review_classification") == EXPECTED_REVIEW_CLASSIFICATION,
        "review_selected_this_execution": review.get("selected_next_target") == CONSUMED_TARGET,
        "weak_strong_attempt_authorized": review.get(
            "weak_strong_conservation_comparison_scope_assumption_reduction_attempt_authorized"
        )
        is True,
        "weak_strong_attempt_not_previously_executed": (
            review.get("weak_strong_conservation_comparison_scope_assumption_reduction_attempt_executed")
            is False
        ),
        "blocker_preserved": review.get("selected_blocker") == BLOCKER
        and review.get("conservation_blocker_remains") is True,
        "family_preserved": review.get("selected_assumption_family") == SELECTED_ASSUMPTION_FAMILY,
        "prior_completed_families_preserved": review.get("completed_prior_assumption_families")
        == PRIOR_COMPLETED_FAMILIES
        and review.get("completed_prior_assumption_family_count") == len(PRIOR_COMPLETED_FAMILIES),
        "selected_row_preserved": review.get("selected_bounded_mathematical_regularity_assumption_row")
        == SELECTED_ROW_ID
        and review.get("selected_row_count") == 1,
        "scope_fields_preserved": review.get("weak_conservation_scope") == WEAK_CONSERVATION_SCOPE
        and review.get("strong_conservation_scope") == STRONG_CONSERVATION_SCOPE
        and review.get("comparison_scope_boundaries") == COMPARISON_SCOPE_BOUNDARIES,
        "classification_authorized": RESULT_CLASSIFICATION
        in review.get("authorized_attempt_result_classifications", []),
        "exactly_one_classification_selected": sum(
            1 for row in classification_rows if row["selected"]
        )
        == 1,
        "no_mathematical_regularity_family_discharge": review.get(
            "mathematical_regularity_assumptions_discharged"
        )
        is False
        and review.get("mathematical_regularity_assumptions_reduced_or_discharged_by_review")
        is False,
        "no_state_admissibility_claim": review.get("state_admissibility_claimed") is False,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed") is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_proof": review.get("conservation_proved") is False
        and review.get("actual_conservation_claimed") is False,
        "no_conservation_proof_object_constructed": review.get("conservation_proof_object_constructed")
        is False
        and review.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": review.get("conservation_witness_constructed")
        is False,
        "no_bianchi_compatibility_claim": review.get("Bianchi_compatibility_claimed") is False,
        "no_semiclassical_einstein_derivation": review.get("semiclassical_einstein_equation_derived")
        is False,
        "no_qft_gr_seam_closure": review.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": review.get("empirical_validation_claimed") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": review.get("release_assembly_authorized") is False
        and review.get("release_packet_assembled") is False
        and review.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    executed = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": executed,
        "accepted": executed,
        "outcome_id": OUTCOME_ID
        if executed
        else "QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_BLOCKED",
        "consumes_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review": (
            EXPECTED_REVIEW_ID
        ),
        "consumes_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result_review_pointer": _ptr(
            review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get("result_review_classification"),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "current_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "operator_domain_assumptions_completed": True,
        "renormalization_assumptions_completed": True,
        "state_domain_assumptions_completed": True,
        "selected_mathematical_regularity_assumption_row": SELECTED_ROW_ID,
        "selected_bounded_mathematical_regularity_assumption_row": SELECTED_ROW_ID,
        "selected_row_count": 1,
        "selected_row_is_repo_authoritative_next_row": True,
        "weak_strong_conservation_comparison_scope": SELECTED_ROW_OBJECT,
        "weak_conservation_scope": WEAK_CONSERVATION_SCOPE,
        "strong_conservation_scope": STRONG_CONSERVATION_SCOPE,
        "comparison_scope_boundaries": COMPARISON_SCOPE_BOUNDARIES,
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "attempt_scope": (
            "EXECUTE_BOUNDED_QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_"
            "ASSUMPTION_REDUCTION_ATTEMPT_ONLY"
        ),
        "result_classification": RESULT_CLASSIFICATION,
        "result_classification_count": 1 if executed else 0,
        "classification_options": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "weak_strong_conservation_comparison_scope_reduction_contract": reduction_contract,
        "weak_strong_conservation_comparison_scope_contract_id": (
            WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_CONTRACT_ID
        ),
        "bounded_weak_strong_conservation_comparison_scope_contract_status": (
            BOUNDED_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_CONTRACT_STATUS
        ),
        "execution_findings": execution_findings,
        "weak_strong_conservation_comparison_scope_assumption_reduction_attempt_started": executed,
        "weak_strong_conservation_comparison_scope_assumption_reduction_attempt_executed": executed,
        "weak_strong_conservation_comparison_scope_assumption_reduced_pending_result_review": executed,
        "weak_strong_conservation_comparison_scope_assumption_obstruction_identified": False,
        "weak_strong_conservation_comparison_scope_assumption_inconclusive": False,
        "weak_strong_conservation_comparison_scope_assumption_reduced_by_attempt": executed,
        "weak_strong_conservation_comparison_scope_assumption_discharged": False,
        "weak_strong_conservation_comparison_scope_assumption_discharged_by_attempt": False,
        "weak_strong_conservation_comparison_scope_reduced_or_discharged_by_attempt": False,
        "weak_strong_conservation_comparison_scope_reduced_or_discharged_by_implication": False,
        "weak_strong_conservation_scope_globally_solved": False,
        "weak_strong_conservation_scope_globally_solved_by_attempt": False,
        "mathematical_regularity_assumptions_discharged": False,
        "mathematical_regularity_assumptions_reduced_or_discharged_by_attempt": False,
        "weak_conservation_proved": False,
        "strong_conservation_proved": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "conservation_proved": False,
        "state_admissibility_claimed": False,
        "state_admissibility_discharged": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "assumption_discharge_claimed": False,
        "assumptions_reduced_or_discharged_by_implication": False,
        "proof_object_constructed": False,
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
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if executed
        else "REMEDIATE_QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT",
        "selected_next_target_kind": (
            "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_"
            "attempt_result_review"
        ),
        "selected_route": (
            "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_"
            "attempt_result_review_after_execution"
        ),
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE_ASSUMPTION_"
            "REDUCTION_ATTEMPT_RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_"
            "SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This execution reduces only MR-ASSUMP-002 to a bounded repo-local "
            "weak/strong conservation-comparison scope contract pending result "
            "review. It does not prove weak or strong conservation, claim state "
            "admissibility, claim source admissibility, prove conservation, "
            "construct a conservation proof object or witness, claim Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR MR-ASSUMP-002 weak/strong conservation comparison "
            "scope assumption-reduction attempt."
        )
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt(
        review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt_report: "
        f"executed={payload['executed']} classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
