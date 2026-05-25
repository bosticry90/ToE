from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_EXECUTION_TARGET,
    OUTCOME_ID as EXPECTED_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_REVIEW_ID,
    SCHEMA_ID as EXPECTED_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT_"
    "20260525_v0"
)
ATTEMPT_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT_v0"
)
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT_"
    "EXECUTED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
)
CONSUMED_TARGET = EXPECTED_EXECUTION_TARGET
NEXT_TARGET = (
    "review_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result"
)
RESULT_CLASSIFICATION = (
    "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_identified_requires_refinement"
)
EXECUTION_CLASSIFICATIONS = [
    "qft_gr_covariant_conservation_statement_with_operator_domain_witness_constructed_pending_result_review",
    RESULT_CLASSIFICATION,
    "qft_gr_covariant_conservation_statement_with_operator_domain_inconclusive_requires_assumption_reduction",
]
SCIENTIFIC_QUESTION = (
    "Can the formulated covariant conservation statement under the accepted "
    "operator-domain structure be witnessed for the candidate QFT-GR "
    "stress-energy source?"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT_20260525_v0.json"
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
            "reason": "The bounded witness attempt result must be reviewed before refinement or assumption reduction routing.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet",
            "decision": "deferred",
            "reason": "Refinement requires acceptance of this attempt result review.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Expectation-domain refinement is not selected before result review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "A bounded witness-attempt obstruction does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this bounded attempt.",
        },
    ]


def build_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    candidate_next_targets = _candidate_next_targets()
    classification_rows = [
        {
            "classification": EXECUTION_CLASSIFICATIONS[0],
            "selected": False,
            "meaning": "A bounded conservation witness under the accepted operator-domain structure was constructed pending result review.",
        },
        {
            "classification": RESULT_CLASSIFICATION,
            "selected": True,
            "meaning": "The statement is formulated, but the repo still lacks the proof object needed to witness it for the candidate source.",
        },
        {
            "classification": EXECUTION_CLASSIFICATIONS[2],
            "selected": False,
            "meaning": "The attempt cannot decide the statement without reducing assumptions.",
        },
    ]
    obstruction_findings = [
        "The accepted packet formulates a bounded covariant-divergence-zero statement under the operator-domain structure.",
        "No repo-local theorem currently proves the formulated statement for the candidate renormalized stress-energy source.",
        "The candidate source remains linked to source admissibility and Bianchi compatibility only as downstream dependencies, not as established consequences.",
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
        "statement_formulation_accepted": review.get("statement_formulation_accepted")
        is True,
        "exactly_one_classification_selected": sum(
            1 for row in classification_rows if row["selected"]
        )
        == 1
        and RESULT_CLASSIFICATION in EXECUTION_CLASSIFICATIONS,
        "obstruction_distinguished_from_construction_and_inconclusive": all(
            row["selected"] == (row["classification"] == RESULT_CLASSIFICATION)
            for row in classification_rows
        ),
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
        else "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT_BLOCKED",
        "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_packet_result_review": EXPECTED_REVIEW_ID,
        "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_packet_result_review_pointer": _ptr(
            review_path
        ),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "scientific_question": SCIENTIFIC_QUESTION,
        "attempt_scope": (
            "EXECUTE_BOUNDED_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT_ONLY"
        ),
        "result_classification": RESULT_CLASSIFICATION,
        "result_classification_count": 1 if executed else 0,
        "classification_options": EXECUTION_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "constructed_witness_result": False,
        "obstruction_identified_result": True,
        "inconclusive_result": False,
        "obstruction_findings": obstruction_findings,
        "covariant_conservation_statement_with_operator_domain_witness_attempt_executed": executed,
        "covariant_conservation_statement_with_operator_domain_witness_constructed": False,
        "covariant_conservation_statement_attempted": True,
        "covariant_conservation_statement_proved": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
        "source_admissibility_claim_limited_to_bounded_result": True,
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
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_WITNESS_ATTEMPT",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review"
        ),
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_"
            "WITNESS_ATTEMPT_RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This execution records an obstruction in the bounded witness "
            "attempt for the formulated covariant conservation statement under "
            "the accepted operator-domain structure. It does not construct a "
            "conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation statement with operator-domain witness attempt."
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt(
        review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_report: "
        f"executed={payload['executed']} classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
