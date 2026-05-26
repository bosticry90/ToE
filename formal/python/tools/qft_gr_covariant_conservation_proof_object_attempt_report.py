from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_proof_object_packet_report import (
    COVARIANT_CONSERVATION_STATEMENT,
    SELECTED_OBSTRUCTION,
    TARGET_PROOF_OBJECT,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_packet_result_review_report import (
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
SCHEMA_ID = "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_20260525_v0"
ATTEMPT_ID = "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_EXECUTED_WITH_NO_"
    "QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
)
CONSUMED_TARGET = EXPECTED_EXECUTION_TARGET
NEXT_TARGET = "review_qft_gr_covariant_conservation_proof_object_attempt_result"
RESULT_CLASSIFICATION = (
    "qft_gr_covariant_conservation_proof_object_obstruction_identified_requires_refinement"
)
EXECUTION_CLASSIFICATIONS = [
    "qft_gr_covariant_conservation_proof_object_constructed_pending_result_review",
    RESULT_CLASSIFICATION,
    "qft_gr_covariant_conservation_proof_object_inconclusive_requires_assumption_reduction",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_20260525_v0.json"
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
            "reason": "The bounded proof-object attempt result must be reviewed before refinement or assumption-reduction routing.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet",
            "decision": "deferred",
            "reason": "Refinement requires result-review acceptance of the obstruction classification.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_proof_object_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Assumption reduction is not selected before result review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "A bounded proof-object attempt obstruction does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this bounded attempt.",
        },
    ]


def build_qft_gr_covariant_conservation_proof_object_attempt(
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
            "meaning": "A conservation proof object was constructed pending result review.",
        },
        {
            "classification": RESULT_CLASSIFICATION,
            "selected": True,
            "meaning": "The proof-object attempt found that the prepared theorem shape still lacks a repo-local proof object under the current assumptions.",
        },
        {
            "classification": EXECUTION_CLASSIFICATIONS[2],
            "selected": False,
            "meaning": "The attempt cannot distinguish construction from obstruction without assumption reduction.",
        },
    ]
    obstruction_findings = [
        "The result review authorizes a bounded proof-object attempt only.",
        "The target theorem shape is available as a prepared statement, not as a constructed proof object.",
        "No repo-local Lean theorem currently proves the covariant-divergence-zero statement for the candidate source under the prepared operator-domain assumptions.",
        "A conservation witness, source admissibility route, and Bianchi compatibility route remain downstream of a reviewed proof-object result.",
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
        "proof_object_attempt_authorized": review.get(
            "bounded_proof_object_attempt_authorized"
        )
        is True,
        "selected_obstruction_preserved": review.get("selected_obstruction")
        == SELECTED_OBSTRUCTION,
        "target_proof_object_preserved": review.get("target_proof_object")
        == TARGET_PROOF_OBJECT,
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
        else "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_BLOCKED",
        "consumes_qft_gr_covariant_conservation_proof_object_packet_result_review": EXPECTED_REVIEW_ID,
        "consumes_qft_gr_covariant_conservation_proof_object_packet_result_review_pointer": _ptr(
            review_path
        ),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "selected_obstruction": SELECTED_OBSTRUCTION,
        "target_proof_object": TARGET_PROOF_OBJECT,
        "covariant_conservation_statement_to_be_proved": COVARIANT_CONSERVATION_STATEMENT,
        "attempt_scope": (
            "EXECUTE_BOUNDED_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_ONLY"
        ),
        "result_classification": RESULT_CLASSIFICATION,
        "result_classification_count": 1 if executed else 0,
        "classification_options": EXECUTION_CLASSIFICATIONS,
        "classification_rows": classification_rows,
        "constructed_proof_object_result": False,
        "obstruction_identified_result": True,
        "inconclusive_result": False,
        "obstruction_findings": obstruction_findings,
        "proof_object_attempt_executed": executed,
        "conservation_proof_object_constructed": False,
        "proof_object_constructed_pending_result_review": False,
        "conservation_witness_constructed": False,
        "conservation_witness_upgraded_by_execution": False,
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
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_proof_object_attempt_result_review"
        ),
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_RESULT_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This execution records an obstruction in the bounded conservation "
            "proof-object attempt. It does not construct a proof object or "
            "conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_proof_object_attempt(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_proof_object_attempt(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation proof-object attempt."
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_proof_object_attempt(
        review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_proof_object_attempt_report: "
        f"executed={payload['executed']} classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
