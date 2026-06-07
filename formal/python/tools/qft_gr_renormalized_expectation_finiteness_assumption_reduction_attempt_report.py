from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    FINITENESS_REGULARITY_BOUNDARY,
    RENORMALIZED_EXPECTATION_DOMAIN,
    RENORMALIZED_STRESS_ENERGY_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROWS,
    CANDIDATE_REDUCTION_ROUTE,
    DEFAULT_CAPTURED_AT_UTC,
    FINITENESS_REGULARITY_BOUNDARY_SCOPE,
    FINITENESS_REGULARITY_CONDITION_STATUS,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_result_review_report import (
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
    "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_"
    "20260606_v0"
)
ATTEMPT_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_v0"
)
OUTCOME_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_FINITE_REGULARITY_ASSUMPTION_REDUCTION_"
    "ATTEMPT_EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
CONSUMED_TARGET = EXPECTED_EXECUTION_TARGET
NEXT_TARGET = (
    "review_qft_gr_renormalized_expectation_finiteness_assumption_reduction_"
    "attempt_result"
)
RESULT_CLASSIFICATION = (
    "qft_gr_renormalized_expectation_finiteness_assumption_reduced_pending_"
    "result_review"
)
FINITENESS_REGULARITY_CONTRACT_ID = (
    "RN-ASSUMP-004-finiteness_regular_boundary_contract_v0"
)
BOUNDED_FINITENESS_REGULARITY_CONTRACT_STATUS = (
    "bounded_repo_local_finiteness_regular_boundary_contract_pending_result_"
    "review_not_finiteness_regular_boundary_discharge"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_20260606_v0.json"
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
                "The bounded RN-ASSUMP-004 finiteness/regularity attempt must "
                "be result-reviewed before conservation, source admissibility, "
                "Bianchi compatibility, or seam-closure work."
            ),
        },
        {
            "target": "discharge_qft_gr_renormalized_expectation_finiteness_assumption",
            "decision": "not_authorized",
            "reason": (
                "Reducing the bounded finiteness/regularity row pending review "
                "does not discharge finiteness or regularity assumptions."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": (
                "Reducing the bounded finiteness/regularity row does not "
                "construct a conservation proof object."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": (
                "No conservation witness is constructed or authorized by this "
                "bounded assumption-row attempt."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": (
                "The bounded finiteness/regularity contract is not a "
                "source-admissibility claim."
            ),
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": (
                "The bounded finiteness/regularity contract is not a Bianchi "
                "compatibility claim."
            ),
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
            "reason": (
                "Release assembly and public submission are not authorized by "
                "this bounded attempt."
            ),
        },
    ]


def build_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt(
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
                "The RN-ASSUMP-004 finiteness/regularity assumption has been "
                "reduced to a bounded repo-local boundary contract pending "
                "result review, without discharging finiteness/regularity or "
                "proving conservation."
            ),
        },
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[1],
            "selected": False,
            "meaning": (
                "The attempt found an obstruction requiring refinement before "
                "the finiteness/regularity boundary could be reduced."
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
        "contract_id": FINITENESS_REGULARITY_CONTRACT_ID,
        "assumption_id": SELECTED_ROW_ID,
        "assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "candidate_stress_energy_object": RENORMALIZED_STRESS_ENERGY_OBJECT,
        "renormalized_expectation_domain": RENORMALIZED_EXPECTATION_DOMAIN,
        "finiteness_regular_boundary": FINITENESS_REGULARITY_BOUNDARY,
        "finiteness_regular_boundary_condition": FINITENESS_REGULARITY_BOUNDARY,
        "scope_boundaries": FINITENESS_REGULARITY_BOUNDARY_SCOPE,
        "contract_status": BOUNDED_FINITENESS_REGULARITY_CONTRACT_STATUS,
        "source_packet_finiteness_regular_boundary_status": (
            FINITENESS_REGULARITY_CONDITION_STATUS
        ),
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "available_repo_evidence": review.get(
            "renormalized_expectation_finiteness_status_tokens", []
        ),
        "claim_ceiling": (
            "finiteness_regular_boundary_contract_pending_result_review_only_"
            "no_finiteness_regular_boundary_discharge_no_conservation_proof_"
            "no_conservation_witness_no_source_admissibility_no_bianchi_"
            "compatibility_no_qft_gr_seam_closure"
        ),
    }
    execution_findings = [
        "The attempt consumes the RN-ASSUMP-004 packet result review and keeps finiteness_regular_boundary as the only executed row.",
        "The bounded repo-local boundary separates finiteness/regularity prerequisites from conservation, source-admissibility, and Bianchi claims.",
        "The bounded boundary contract preserves RN-ASSUMP-001, RN-ASSUMP-002, and RN-ASSUMP-003 as accepted prior rows and operator-domain closeout as prior family context.",
        "The reduction is pending result review and does not construct a conservation proof object or conservation witness.",
    ]
    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("review_id")
        == EXPECTED_REVIEW_ID,
        "review_schema_expected": review.get("schema_id") == EXPECTED_REVIEW_SCHEMA_ID,
        "review_outcome_expected": review.get("outcome_id") == EXPECTED_REVIEW_OUTCOME,
        "review_classification_expected": review.get("result_review_classification")
        == EXPECTED_REVIEW_CLASSIFICATION,
        "review_selected_this_execution": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "bounded_reduction_attempt_authorized": review.get(
            "bounded_reduction_attempt_authorized"
        )
        is True,
        "bounded_reduction_attempt_not_previously_executed": review.get(
            "bounded_reduction_attempt_executed"
        )
        is False,
        "blocker_preserved": review.get("selected_blocker") == BLOCKER
        and review.get("conservation_blocker_remains") is True,
        "family_preserved": review.get("selected_assumption_family")
        == SELECTED_ASSUMPTION_FAMILY,
        "prior_operator_domain_family_accepted": review.get(
            "prior_operator_domain_assumptions_accepted"
        )
        is True,
        "prior_rn_assump_001_002_003_accepted": review.get(
            "accepted_prior_renormalization_assumption_rows"
        )
        == ACCEPTED_PRIOR_ROWS,
        "selected_row_preserved": review.get("selected_renormalization_assumption_row")
        == SELECTED_ROW_ID
        and review.get("selected_row_count") == 1,
        "finiteness_regular_boundary_preserved": review.get(
            "finiteness_regular_boundary"
        )
        == FINITENESS_REGULARITY_BOUNDARY
        and review.get("finiteness_regular_boundary_condition")
        == FINITENESS_REGULARITY_BOUNDARY,
        "finiteness_regular_boundary_status_not_discharged": review.get(
            "finiteness_regular_boundary_status"
        )
        == FINITENESS_REGULARITY_CONDITION_STATUS,
        "scope_boundaries_preserved": review.get("scope_boundaries")
        == FINITENESS_REGULARITY_BOUNDARY_SCOPE,
        "classification_authorized": RESULT_CLASSIFICATION
        in review.get("authorized_attempt_result_classifications", []),
        "exactly_one_classification_selected": sum(
            1 for row in classification_rows if row["selected"]
        )
        == 1,
        "does_not_discharge_finiteness_regular_boundary_by_implication": True,
        "no_finiteness_regular_boundary_discharge": review.get(
            "finiteness_regular_boundary_discharged"
        )
        is False,
        "no_conservation_proof": review.get("conservation_proved") is False
        and review.get("actual_conservation_claimed") is False,
        "no_conservation_proof_object_constructed": review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and review.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": review.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_bianchi_compatibility_claim": review.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_derivation": review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": review.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": review.get("empirical_validation_claimed") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": review.get("release_assembly_authorized")
        is False
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
        else "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_BLOCKED",
        "consumes_qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_result_review": (
            EXPECTED_REVIEW_ID
        ),
        "consumes_qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_result_review_pointer": _ptr(
            review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "current_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "prior_completed_family": "operator_domain_assumptions",
        "prior_operator_domain_assumptions_accepted": True,
        "accepted_prior_renormalization_assumption_rows": ACCEPTED_PRIOR_ROWS,
        "selected_renormalization_assumption_row": SELECTED_ROW_ID,
        "candidate_stress_energy_object": RENORMALIZED_STRESS_ENERGY_OBJECT,
        "renormalized_expectation_domain": RENORMALIZED_EXPECTATION_DOMAIN,
        "finiteness_regular_boundary": FINITENESS_REGULARITY_BOUNDARY,
        "finiteness_regular_boundary_condition": FINITENESS_REGULARITY_BOUNDARY,
        "source_packet_finiteness_regular_boundary_status": (
            FINITENESS_REGULARITY_CONDITION_STATUS
        ),
        "scope_boundaries": FINITENESS_REGULARITY_BOUNDARY_SCOPE,
        "bounded_finiteness_regular_boundary_contract_status": (
            BOUNDED_FINITENESS_REGULARITY_CONTRACT_STATUS
        ),
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "attempt_scope": (
            "EXECUTE_BOUNDED_QFT_GR_RENORMALIZED_EXPECTATION_FINITE_REGULARITY_"
            "ASSUMPTION_REDUCTION_ATTEMPT_ONLY"
        ),
        "result_classification": RESULT_CLASSIFICATION,
        "result_classification_count": 1 if executed else 0,
        "classification_options": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "finiteness_regular_boundary_reduction_contract": reduction_contract,
        "execution_findings": execution_findings,
        "finiteness_regular_boundary_assumption_reduction_attempt_executed": executed,
        "finiteness_regular_boundary_assumption_reduced_pending_result_review": (
            executed
        ),
        "finiteness_regular_boundary_assumption_obstruction_identified": False,
        "finiteness_regular_boundary_assumption_inconclusive": False,
        "finiteness_regular_boundary_assumption_reduced_by_attempt": executed,
        "finiteness_regular_boundary_assumption_discharged": False,
        "finiteness_regular_boundary_assumption_discharged_by_attempt": False,
        "finiteness_regular_boundary_reduced_or_discharged_by_attempt": False,
        "finiteness_regular_boundary_reduced_or_discharged_by_implication": False,
        "finiteness_regular_boundary_discharged": False,
        "finiteness_regular_boundary_discharged_by_implication": False,
        "finiteness_regular_boundary_claimed_as_conservation_proof": False,
        "finiteness_regular_boundary_claimed_as_conservation_source": False,
        "finiteness_regular_boundary_claimed_as_source_admissibility": False,
        "finiteness_regular_boundary_claimed_as_bianchi_compatibility": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "conservation_proved": False,
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
        else "REMEDIATE_QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT",
        "selected_next_target_kind": (
            "qft_gr_renormalized_expectation_finiteness_assumption_reduction_"
            "attempt_result_review"
        ),
        "selected_route": (
            "qft_gr_renormalized_expectation_finiteness_assumption_reduction_"
            "attempt_result_review_after_execution"
        ),
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_"
            "REDUCTION_ATTEMPT_RESULT_ONLY_NO_FINITENESS_REGULARITY_DISCHARGE_"
            "CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This execution reduces only RN-ASSUMP-004 to a bounded repo-local "
            "finiteness/regularity boundary contract pending result review. It "
            "does not discharge finiteness or regularity assumptions, construct "
            "a conservation proof object or conservation witness, claim source "
            "admissibility, claim Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR RN-ASSUMP-004 finiteness/regularity "
            "assumption-reduction attempt."
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
    payload = write_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt(
        review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_report: "
        f"executed={payload['executed']} classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
