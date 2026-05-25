from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REFINED_OBSTRUCTION_CLASS,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_"
    "REFINEMENT_PACKET_20260525_v0"
)
PACKET_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_"
    "REFINEMENT_PACKET_v0"
)
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_"
    "REFINEMENT_PACKET_PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
)
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_"
    "refinement_packet_prepared_primary_missing_conservation_proof_object_no_closure_or_empirical_validation"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = (
    "review_qft_gr_covariant_conservation_statement_with_operator_domain_"
    "obstruction_refinement_packet_result"
)
PRIMARY_OBSTRUCTION_ID = (
    "qft_gr_covariant_conservation_statement_with_operator_domain_missing_conservation_"
    "proof_object_v0"
)
PRIMARY_MISSING_CONDITION = REFINED_OBSTRUCTION_CLASS
AVAILABLE_STRUCTURE = "covariant_conservation_statement_with_operator_domain"
MISSING_PROOF_OBJECT = (
    "conservation_proof_object_for_candidate_source_under_prepared_operator_domain"
)
REQUIRED_THEOREM_SHAPE = (
    "candidate_stress_energy_source_in_prepared_operator_domain -> "
    "covariant_divergence candidate_stress_energy_source = 0"
)
REQUIRED_ASSUMPTIONS = (
    "selected stress-energy object, state-expectation semantics, "
    "operator-domain membership, renormalization scope, and conservation-law "
    "premise are all available under one bounded theorem statement"
)
REQUIRED_LEAN_SURFACE = (
    "ToeFormal.Bridges.QFT_GR_CovariantConservationStatementWithOperatorDomainWitnessAttempt"
)
FAILURE_MODE_IF_UNRESOLVED = (
    "the operator-domain conservation statement remains formulated but "
    "unwitnessed, blocking source-admissibility and Bianchi routes"
)
CLAIM_CEILING = "refinement_packet_only_no_conservation_witness_or_seam_closure"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_REFINEMENT_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _refinement_rows() -> list[dict[str, str]]:
    row_data = [
        (
            PRIMARY_OBSTRUCTION_ID,
            PRIMARY_MISSING_CONDITION,
            "primary",
            "Covariant conservation statement with operator-domain structure is formulated and accepted, but the witness attempt found no repo-local theorem proving the statement for the candidate renormalized stress-energy source.",
            "theorem: candidate stress-energy source in prepared operator domain implies covariant divergence zero under explicitly bounded assumptions",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationStatementWithOperatorDomainWitnessAttempt",
            "selected stress-energy object, state-expectation semantics, operator-domain membership, and conservation-law premise are all available under one bounded theorem statement",
            "the conservation statement remains formulated but unwitnessed, blocking source-admissibility and Bianchi routes",
            "prepare_qft_gr_covariant_conservation_proof_object_packet",
        ),
        (
            "qft_gr_covariant_conservation_statement_with_operator_domain_operator_domain_still_insufficient_v0",
            "operator_domain_still_insufficient",
            "secondary",
            "The operator-domain packet may still be too schematic to support the proof object required by the statement.",
            "domain-strengthening lemma or packet specifying exact membership/regularity predicates",
            "ToeFormal.Bridges.QFT_GR_CovariantDerivativeOperatorDomainPacket",
            "the prepared domain includes all objects used by the conservation theorem",
            "the proof object cannot type-check or cannot apply to the candidate source",
            "deferred unless the proof-object packet exposes domain insufficiency as primary",
        ),
        (
            "qft_gr_covariant_conservation_statement_with_operator_domain_missing_law_v0",
            "missing_conservation_law_over_selected_domain",
            "secondary",
            "No conservation law has been supplied over the selected domain for the candidate source.",
            "bounded conservation-law premise or obstruction packet for the selected stress-energy object",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
            "the selected source satisfies a conservation identity under explicit assumptions",
            "the theorem shape has hypotheses but no law that can discharge them",
            "deferred until proof-object packet chooses whether to assume or prove the law",
        ),
        (
            "qft_gr_covariant_conservation_statement_with_operator_domain_expectation_stability_v0",
            "renormalized_expectation_not_stable_under_covariant_derivative",
            "secondary",
            "The renormalized expectation is not yet shown stable under the selected covariant derivative/divergence.",
            "stability lemma linking renormalized expectation semantics to the selected derivative",
            "ToeFormal.Bridges.QFT_GR_RenormalizedExpectationValueSemantics",
            "renormalization/state domain preserves the derivative operation used in the statement",
            "divergence-zero cannot be proved for the renormalized expectation object",
            "deferred as possible follow-on refinement",
        ),
        (
            "qft_gr_covariant_conservation_statement_with_operator_domain_weak_strong_mismatch_v0",
            "weak_strong_conservation_mismatch",
            "secondary",
            "The theorem may need to choose strong covariant divergence or weak/distributional conservation.",
            "form-selection proof object distinguishing strong and weak conservation targets",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationStatementWithOperatorDomainPacket",
            "the selected regularity/distributional scope matches the theorem target",
            "a later proof could witness the wrong conservation form",
            "deferred until proof-object theorem shape is reviewed",
        ),
        (
            "qft_gr_covariant_conservation_statement_with_operator_domain_bianchi_conditional_v0",
            "Bianchi_compatibility_still_conditional",
            "downstream",
            "Bianchi compatibility remains downstream even if the conservation proof object is later supplied.",
            "Bianchi compatibility dependency packet after conservation proof-object review",
            "ToeFormal.Bridges.QFT_GR_BianchiCompatibilityObligationSemantics",
            "accepted conservation witness can be related to the contracted Bianchi identity boundary",
            "Bianchi compatibility remains unclaimed and cannot be imported into this packet",
            "deferred; no Bianchi compatibility claim authorized",
        ),
    ]
    return [
        {
            "obstruction_id": row[0],
            "missing_condition": row[1],
            "priority": row[2],
            "available_structure": row[3],
            "required_theorem_shape": row[4],
            "required_Lean_surface": row[5],
            "required_assumptions": row[6],
            "failure_mode_if_unresolved": row[7],
            "claim_ceiling": "refinement_packet_only_no_conservation_witness_or_seam_closure",
            "next_bounded_action": row[8],
        }
        for row in row_data
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The proof-object refinement packet must be reviewed before preparing a proof-object packet.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_proof_object_packet",
            "decision": "deferred",
            "reason": "Proof-object packet preparation requires acceptance of this refinement packet.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Expectation-domain refinement is deferred unless selected after this packet review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Obstruction refinement does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this packet.",
        },
    ]


def build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    rows = _refinement_rows()
    candidate_next_targets = _candidate_next_targets()
    selected_rows = [
        row for row in rows if row["obstruction_id"] == PRIMARY_OBSTRUCTION_ID
    ]
    acceptance_criteria = {
        "consumes_expected_result_review": review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "refined_obstruction_preserved": review.get("refined_obstruction_class")
        == REFINED_OBSTRUCTION_CLASS,
        "exactly_one_primary_obstruction_selected": len(selected_rows) == 1
        and selected_rows[0]["missing_condition"] == PRIMARY_MISSING_CONDITION,
        "row_structure_complete": all(
            {
                "obstruction_id",
                "missing_condition",
                "priority",
                "available_structure",
                "required_theorem_shape",
                "required_Lean_surface",
                "required_assumptions",
                "failure_mode_if_unresolved",
                "claim_ceiling",
                "next_bounded_action",
            }
            <= set(row)
            for row in rows
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_REFINEMENT_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "selected_obstruction": PRIMARY_MISSING_CONDITION,
        "available_structure": AVAILABLE_STRUCTURE,
        "missing_proof_object": MISSING_PROOF_OBJECT,
        "required_theorem_shape": REQUIRED_THEOREM_SHAPE,
        "required_assumptions": REQUIRED_ASSUMPTIONS,
        "required_Lean_surface": REQUIRED_LEAN_SURFACE,
        "failure_mode_if_unresolved": FAILURE_MODE_IF_UNRESOLVED,
        "claim_ceiling": CLAIM_CEILING,
        "next_bounded_action": NEXT_TARGET,
        "primary_obstruction_id": PRIMARY_OBSTRUCTION_ID,
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_solved": False,
        "refinement_rows": rows,
        "prepares_refinement_only": True,
        "covariant_conservation_statement_with_operator_domain_witness_constructed": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
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
        if prepared
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_REFINEMENT_PACKET",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_"
            "OBSTRUCTION_REFINEMENT_PACKET_RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet refines the post-operator-domain obstruction to the "
            "missing conservation proof object. It defines the required theorem "
            "shape, assumptions, Lean surface, failure mode, claim ceiling, and "
            "next bounded action, but does not construct a conservation "
            "witness, claim source admissibility or Bianchi compatibility, "
            "derive the semiclassical Einstein equation, close QFT-GR, "
            "validate empirically, promote the master action, assemble release, "
            "or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation statement with operator-domain obstruction refinement packet."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
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
    payload = write_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_report: "
        f"prepared={payload['prepared']} primary={payload['primary_missing_condition']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
