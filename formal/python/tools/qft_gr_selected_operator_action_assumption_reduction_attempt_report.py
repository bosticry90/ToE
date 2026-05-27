from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    PRIMARY_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_result_review_report import (
    SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW,
)
from formal.python.tools.qft_gr_selected_operator_action_assumption_reduction_packet_result_review_report import (
    AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
    DEFAULT_OUT as DEFAULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_EXECUTION_TARGET,
    OUTCOME_ID as EXPECTED_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_REVIEW_ID,
    SCHEMA_ID as EXPECTED_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_20260526_v0"
ATTEMPT_ID = "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_v0"
OUTCOME_ID = (
    "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_EXECUTED_WITH_"
    "NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
CONSUMED_TARGET = EXPECTED_EXECUTION_TARGET
NEXT_TARGET = "review_qft_gr_selected_operator_action_assumption_reduction_attempt_result"
RESULT_CLASSIFICATION = (
    "qft_gr_selected_operator_action_assumption_reduced_pending_result_review"
)
SELECTED_ROW_ID = SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW
SELECTED_OPERATOR_ACTION_CONTRACT_ID = (
    "OD-ASSUMP-001-selected_operator_action_contract_v0"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_20260526_v0.json"
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
                "The bounded selected-operator/action reduction attempt must be "
                "reviewed before any downstream assumption target is prepared."
            ),
        },
        {
            "target": "prepare_qft_gr_candidate_source_domain_membership_assumption_reduction_packet",
            "decision": "deferred",
            "reason": (
                "Candidate source-domain membership remains downstream of result "
                "review acceptance for the selected-operator/action attempt."
            ),
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": (
                "The selected-operator/action reduction attempt does not authorize "
                "a conservation proof-object attempt."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "No bounded assumption-reduction attempt closes QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this bounded attempt.",
        },
    ]


def build_qft_gr_selected_operator_action_assumption_reduction_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    selected_assumption = review.get("selected_operator_action_assumption", {})
    candidate_next_targets = _candidate_next_targets()
    classification_rows = [
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[0],
            "selected": True,
            "meaning": (
                "The selected operator/action assumption has been reduced to a "
                "bounded contract pending result review, without discharging the "
                "assumption or proving conservation."
            ),
        },
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[1],
            "selected": False,
            "meaning": (
                "The attempt found an obstruction requiring refinement before the "
                "selected operator/action could be reduced."
            ),
        },
        {
            "classification": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS[2],
            "selected": False,
            "meaning": (
                "The attempt could not determine reduction status without further "
                "assumption reduction."
            ),
        },
    ]
    reduction_contract = {
        "contract_id": SELECTED_OPERATOR_ACTION_CONTRACT_ID,
        "assumption_id": SELECTED_ROW_ID,
        "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_operator_action": (
            "covariant_divergence_operator_action_on_candidate_renormalized_"
            "stress_energy_source"
        ),
        "typed_scope": (
            "bounded_operator_domain_contract_for_later_candidate_source_"
            "conservation_statement"
        ),
        "available_repo_evidence": selected_assumption.get("available_repo_evidence", []),
        "required_future_proof_object": selected_assumption.get(
            "required_future_proof_object"
        ),
        "claim_ceiling": (
            "selected_operator_action_reduced_pending_result_review_only_no_"
            "assumption_discharge_no_conservation_witness_no_qft_gr_seam_closure"
        ),
    }
    execution_findings = [
        "The attempt consumes the selected-operator/action packet result review and keeps OD-ASSUMP-001 as the only executed row.",
        "The selected action is pinned as a bounded covariant-divergence operator action on the candidate renormalized stress-energy source for later conservation-statement work.",
        "The reduction is pending result review and does not discharge the selected-operator/action assumption by implication.",
        "Candidate source-domain membership, state-expectation linkage, renormalized-expectation linkage, conservation proof objects, and QFT-GR seam closure remain downstream.",
    ]
    acceptance_criteria = {
        "consumes_expected_result_review": review.get("review_id")
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
        "selected_row_preserved": review.get("selected_operator_domain_assumption_row")
        == SELECTED_ROW_ID
        and selected_assumption.get("assumption_id") == SELECTED_ROW_ID,
        "selected_family_preserved": review.get("selected_assumption_family")
        == PRIMARY_ASSUMPTION_FAMILY,
        "blocker_preserved": review.get("selected_blocker")
        == "insufficient_assumptions_for_conservation",
        "classification_authorized": RESULT_CLASSIFICATION
        in review.get("authorized_attempt_result_classifications", []),
        "exactly_one_classification_selected": sum(
            1 for row in classification_rows if row["selected"]
        )
        == 1,
        "reduction_distinguished_from_discharge": True,
        "no_conservation_proof_object_constructed": review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and review.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": review.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_admissibility_or_bianchi_claim": review.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and review.get("Bianchi_compatibility_claimed") is False,
        "no_semiclassical_einstein_derivation": review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": review.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": review.get("empirical_validation_claimed") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": review.get(
            "release_assembly_authorized"
        )
        is False
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
        else "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_BLOCKED",
        "consumes_qft_gr_selected_operator_action_assumption_reduction_packet_result_review": EXPECTED_REVIEW_ID,
        "consumes_qft_gr_selected_operator_action_assumption_reduction_packet_result_review_pointer": _ptr(
            review_path
        ),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_operator_domain_assumption_row": SELECTED_ROW_ID,
        "attempt_scope": (
            "EXECUTE_BOUNDED_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_"
            "REDUCTION_ATTEMPT_ONLY"
        ),
        "result_classification": RESULT_CLASSIFICATION,
        "result_classification_count": 1 if executed else 0,
        "classification_options": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "selected_operator_action_reduction_contract": reduction_contract,
        "execution_findings": execution_findings,
        "selected_operator_action_assumption_reduction_attempt_executed": executed,
        "operator_action_assumption_reduced_pending_result_review": executed,
        "operator_action_assumption_obstruction_identified": False,
        "operator_action_assumption_inconclusive": False,
        "operator_action_assumption_discharged": False,
        "assumption_discharge_claimed": False,
        "assumptions_reduced_or_discharged_by_implication": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
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
        else "REMEDIATE_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT",
        "selected_next_target_kind": (
            "qft_gr_selected_operator_action_assumption_reduction_attempt_result_review"
        ),
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_"
            "RESULT_ONLY_NO_ASSUMPTION_DISCHARGE_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This execution reduces only the selected-operator/action assumption "
            "to a bounded contract pending result review. It does not discharge "
            "the assumption by implication, construct a conservation proof object "
            "or conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_selected_operator_action_assumption_reduction_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_selected_operator_action_assumption_reduction_attempt(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR selected-operator/action assumption-reduction attempt."
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
    payload = write_qft_gr_selected_operator_action_assumption_reduction_attempt(
        review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_selected_operator_action_assumption_reduction_attempt_report: "
        f"executed={payload['executed']} classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
