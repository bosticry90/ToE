from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conservation_form_scope_assumption_reduction_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    CONSERVATION_FORM_SCOPE_CONTRACT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_conservation_form_scope_assumption_reduction_packet_report import (
    CONSERVATION_FORM_OPTIONS,
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    PRIOR_ACCEPTED_ROW004,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_BOUNDED_CONSERVATION_FORM,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    PRIMARY_ASSUMPTION_FAMILY,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_20260527_v0"
)
REVIEW_ID = (
    "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_REDUCED_CONSERVATION_FORM_SCOPE_AND_AUTHORIZES_NEXT_OPERATOR_"
    "DOMAIN_ROW_SELECTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review_"
    "accepts_reduced_conservation_form_scope_and_authorizes_next_operator_domain_"
    "row_selection_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW = "OD-ASSUMP-006-metric_connection_scope"
NEXT_TARGET = "prepare_qft_gr_metric_connection_scope_assumption_reduction_packet"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_"
        "RESULT_REVIEW_20260527_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _operator_domain_row_sequence() -> list[str]:
    return [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
        PRIOR_ACCEPTED_ROW004,
        SELECTED_ROW_ID,
        NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The OD-ASSUMP-005 conservation-form-scope reduction is "
                "accepted only as a bounded weak operator-domain conservation "
                "form contract, so the next operator-domain row may be prepared "
                "without proving conservation or claiming Bianchi compatibility."
            ),
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": (
                "Accepting conservation form scope does not authorize a "
                "conservation proof-object attempt."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": (
                "No conservation witness is constructed or authorized by this "
                "bounded result review."
            ),
        },
        {
            "target": "prepare_qft_gr_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "reason": (
                "Accepting conservation form scope does not authorize source "
                "admissibility."
            ),
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": (
                "Metric/connection scope preparation is still below Bianchi "
                "compatibility."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "No operator-domain row result review closes QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is outside this bounded result review.",
        },
    ]


def build_qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    contract = attempt.get("conservation_form_scope_reduction_contract", {})
    candidate_next_targets = _candidate_next_targets()
    row_sequence = _operator_domain_row_sequence()

    acceptance_criteria = {
        "consumes_expected_attempt": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID
        and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID,
        "attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_selected_this_review": attempt.get("selected_next_target")
        == CONSUMED_TARGET,
        "attempt_classification_expected": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "attempt_executed_and_accepted": attempt.get("executed") is True
        and attempt.get("accepted") is True,
        "prior_rows001_002_003_004_preserved": attempt.get(
            "prior_accepted_operator_domain_assumption_rows"
        )
        == [
            PRIOR_ACCEPTED_ROW001,
            PRIOR_ACCEPTED_ROW002,
            PRIOR_ACCEPTED_ROW003,
            PRIOR_ACCEPTED_ROW004,
        ],
        "selected_row_preserved": attempt.get("selected_operator_domain_assumption_row")
        == SELECTED_ROW_ID
        and contract.get("assumption_id") == SELECTED_ROW_ID,
        "selected_family_preserved": attempt.get("selected_assumption_family")
        == PRIMARY_ASSUMPTION_FAMILY
        and contract.get("assumption_family") == PRIMARY_ASSUMPTION_FAMILY,
        "contract_expected": contract.get("contract_id")
        == CONSERVATION_FORM_SCOPE_CONTRACT_ID,
        "conservation_form_options_preserved": attempt.get(
            "conservation_form_options"
        )
        == CONSERVATION_FORM_OPTIONS
        and contract.get("conservation_form_options") == CONSERVATION_FORM_OPTIONS,
        "selected_bounded_form_preserved": attempt.get(
            "selected_bounded_conservation_form"
        )
        == SELECTED_BOUNDED_CONSERVATION_FORM
        and contract.get("selected_bounded_conservation_form")
        == SELECTED_BOUNDED_CONSERVATION_FORM,
        "required_future_proof_object_preserved": attempt.get(
            "required_future_proof_object"
        )
        == REQUIRED_FUTURE_PROOF_OBJECT
        and contract.get("required_future_proof_object")
        == REQUIRED_FUTURE_PROOF_OBJECT,
        "reduced_pending_review_result_accepted": attempt.get(
            "conservation_form_scope_assumption_reduced_pending_result_review"
        )
        is True
        and attempt.get("conservation_form_scope_assumption_obstruction_identified")
        is False
        and attempt.get("conservation_form_scope_assumption_inconclusive") is False,
        "reduction_not_treated_as_conservation_proof": attempt.get(
            "conservation_form_scope_claimed_as_conservation_proof"
        )
        is False
        and attempt.get("actual_conservation_claimed") is False
        and attempt.get("conservation_proved") is False,
        "reduction_not_treated_as_discharge": attempt.get(
            "conservation_form_scope_assumption_discharged"
        )
        is False
        and attempt.get("assumption_discharge_claimed") is False
        and attempt.get("assumptions_reduced_or_discharged_by_implication") is False,
        "no_conservation_proof_object_constructed": attempt.get(
            "conservation_proof_object_constructed"
        )
        is False
        and attempt.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": attempt.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_admissibility_claim": attempt.get("source_admissibility_claimed")
        is False
        and attempt.get("stress_energy_source_admissibility_claimed") is False,
        "no_bianchi_compatibility_claim": attempt.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_derivation": attempt.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": attempt.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": attempt.get("empirical_validation_claimed") is False,
        "no_master_action_promotion": attempt.get("master_action_promoted") is False
        and attempt.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": attempt.get("release_assembly_authorized")
        is False
        and attempt.get("release_packet_assembled") is False
        and attempt.get("public_submission_authorized") is False,
        "next_row_is_sixth_operator_domain_row": row_sequence[5]
        == NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    accepted = all(acceptance_criteria.values())

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
            "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_"
            "RESULT_REVIEW_REJECTS_OR_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_conservation_form_scope_assumption_reduction_attempt_"
            "result_review_rejects_or_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_conservation_form_scope_assumption_reduction_attempt": EXPECTED_ATTEMPT_ID,
        "consumes_qft_gr_conservation_form_scope_assumption_reduction_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "prior_accepted_operator_domain_assumption_rows": [
            PRIOR_ACCEPTED_ROW001,
            PRIOR_ACCEPTED_ROW002,
            PRIOR_ACCEPTED_ROW003,
            PRIOR_ACCEPTED_ROW004,
        ],
        "selected_operator_domain_assumption_row": SELECTED_ROW_ID,
        "conservation_form_options": CONSERVATION_FORM_OPTIONS,
        "selected_bounded_conservation_form": SELECTED_BOUNDED_CONSERVATION_FORM,
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "conservation_form_scope_reduction_contract": contract,
        "accepted_contract_id": CONSERVATION_FORM_SCOPE_CONTRACT_ID if accepted else "",
        "contract_acceptance_scope": (
            "bounded_conservation_form_scope_contract_only_no_conservation_proof_"
            "no_conservation_witness_no_source_admissibility_no_bianchi_compatibility"
        ),
        "operator_domain_row_sequence": row_sequence,
        "completed_operator_domain_row": SELECTED_ROW_ID,
        "next_operator_domain_assumption_row": NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
        "conservation_form_scope_assumption_reduction_attempt_result_reviewed": accepted,
        "conservation_form_scope_assumption_reduction_accepted": accepted,
        "conservation_form_scope_assumption_reduction_rejected": not accepted,
        "conservation_form_scope_assumption_reduced_pending_result_review_accepted": accepted,
        "conservation_form_scope_assumption_discharged": False,
        "conservation_form_scope_assumption_discharged_by_review": False,
        "conservation_form_scope_claimed_as_conservation_proof": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "conservation_proved": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "assumption_discharge_claimed": False,
        "assumptions_reduced_or_discharged_by_review": False,
        "assumptions_reduced_or_discharged_by_implication": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "Bianchi_compatibility_claimed": False,
        "metric_connection_scope_treated_as_bianchi_compatibility": False,
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
        if accepted
        else (
            "REMEDIATE_QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_"
            "ATTEMPT_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "qft_gr_metric_connection_scope_assumption_reduction_packet_preparation"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_PACKET_"
            "ONLY_NO_BIANCHI_COMPATIBILITY_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the reduced OD-ASSUMP-005 "
            "conservation-form-scope contract and authorizes preparation of "
            "the next operator-domain row, OD-ASSUMP-006 metric/connection "
            "scope. It does not prove conservation, construct a conservation "
            "proof object or conservation witness, claim source admissibility "
            "or Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, promote the master "
            "action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review(
            attempt_path=attempt_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR conservation-form-scope assumption-reduction "
            "attempt result review."
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
    payload = write_qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
