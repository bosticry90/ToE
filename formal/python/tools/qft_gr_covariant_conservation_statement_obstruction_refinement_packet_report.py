from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OBSTRUCTION_CLASS as ACCEPTED_OBSTRUCTION_CLASSIFICATION,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REFINEMENT_CANDIDATES,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_OBSTRUCTION_REFINEMENT_PACKET_20260525_v0"
)
PACKET_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_OBSTRUCTION_REFINEMENT_PACKET_v0"
OUTCOME_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_OBSTRUCTION_REFINEMENT_PACKET_PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_statement_obstruction_refinement_packet_prepared_"
    "primary_missing_covariant_derivative_operator_domain_no_closure_or_empirical_validation"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "prepare_qft_gr_covariant_derivative_operator_domain_packet"
PRIMARY_OBSTRUCTION_ID = (
    "qft_gr_covariant_conservation_statement_missing_covariant_derivative_operator_domain_v0"
)
PRIMARY_MISSING_CONDITION = "missing_covariant_derivative_or_operator_domain"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_OBSTRUCTION_REFINEMENT_PACKET_20260525_v0.json"
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
            "The attempt found no repo-local proof object binding the candidate renormalized stress-energy expectation to a selected covariant derivative/divergence operator on a bounded domain.",
            "bounded covariant derivative/divergence operator-domain packet for the candidate stress-energy source",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationStatementWitnessAttempt",
            "a selected connection/divergence operator and domain of applicability are fixed before conservation is stated",
            "without a selected operator/domain, the covariant conservation statement is not a well-typed witness target",
            NEXT_TARGET,
        ),
        (
            "qft_gr_covariant_conservation_statement_weak_strong_ambiguity_v0",
            "weak_vs_strong_conservation_ambiguity",
            "secondary",
            "The packet allows covariant or weak conservation, but the attempt cannot settle form selection while the operator/domain is missing.",
            "bounded form-selection packet distinguishing strong divergence-zero from weak/test-function conservation",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationStatementWitnessPacket",
            "the selected source domain supports the chosen conservation form",
            "later proofs may satisfy a different conservation notion than the intended one",
            "deferred until the operator/domain packet fixes the base statement",
        ),
        (
            "qft_gr_covariant_conservation_statement_state_domain_limitation_v0",
            "state_domain_limitation",
            "secondary",
            "The state-expectation scope remains too broad to prove conservation for all candidate states.",
            "bounded state-domain restriction sufficient for the selected conservation operator",
            "ToeFormal.Bridges.QFT_GR_StateExpectationFunctionalSemantics",
            "the state class preserves the conservation identity required by the selected source",
            "the conservation statement remains too broad for available assumptions",
            "deferred as possible follow-on domain reduction",
        ),
        (
            "qft_gr_covariant_conservation_statement_renormalized_expectation_domain_v0",
            "renormalized_expectation_not_well_defined_enough",
            "secondary",
            "Renormalized expectation semantics are present as prerequisite surfaces but not yet bound to the conservation operator domain.",
            "domain adequacy witness tying renormalized expectation to the selected covariant derivative/divergence operator",
            "ToeFormal.Bridges.QFT_GR_RenormalizedExpectationValueSemantics",
            "renormalized stress-energy expectation is meaningful on the same domain as the conservation operator",
            "the operator may not apply to the candidate expectation",
            "deferred unless the operator/domain packet exposes this as the blocking dependency",
        ),
        (
            "qft_gr_covariant_conservation_statement_absent_selected_law_v0",
            "absence_of_conservation_law_for_selected_stress_energy_object",
            "secondary",
            "No conservation law has been selected for the candidate stress-energy object after the failed witness attempt.",
            "bounded conservation-law premise or obstruction packet for the selected stress-energy object",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
            "the selected stress-energy object satisfies the conservation identity under explicit assumptions",
            "even a well-typed operator/domain would lack the law needed to prove divergence zero",
            "deferred until operator/domain statement is fixed",
        ),
        (
            "qft_gr_covariant_conservation_statement_bianchi_dependency_v0",
            "Bianchi_compatibility_not_derivable_from_current_assumptions",
            "downstream",
            "Bianchi compatibility remains downstream and cannot be inferred from a failed conservation statement attempt.",
            "bounded Bianchi dependency map after conservation statement refinement",
            "ToeFormal.Bridges.QFT_GR_BianchiCompatibilityObligationSemantics",
            "accepted conservation statement can be related to the contracted Bianchi identity boundary",
            "Bianchi compatibility remains unclaimed",
            "deferred; no Bianchi compatibility claim authorized",
        ),
    ]
    return [
        {
            "obstruction_id": row[0],
            "missing_condition": row[1],
            "priority": row[2],
            "available_repo_evidence": row[3],
            "required_future_proof_object": row[4],
            "required_Lean_surface": row[5],
            "required_physics_assumption": row[6],
            "failure_mode_if_unresolved": row[7],
            "claim_ceiling": "refinement_packet_only_no_obstruction_solution_no_conservation_witness",
            "next_bounded_action": row[8],
        }
        for row in row_data
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The primary blocker is the missing covariant derivative/operator domain.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Renormalized expectation domain work may follow if the operator-domain packet exposes it as the next blocker.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_statement_form_selection_packet",
            "decision": "deferred",
            "reason": "Weak-vs-strong conservation selection depends on the operator/domain packet.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Refinement packet preparation does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this packet.",
        },
    ]


def build_qft_gr_covariant_conservation_statement_obstruction_refinement_packet(
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
        "accepted_obstruction_preserved": review.get("obstruction_class")
        == ACCEPTED_OBSTRUCTION_CLASSIFICATION,
        "candidate_menu_preserved": review.get("refinement_candidates")
        == REFINEMENT_CANDIDATES,
        "row_structure_complete": all(
            {
                "obstruction_id",
                "missing_condition",
                "priority",
                "available_repo_evidence",
                "required_future_proof_object",
                "required_Lean_surface",
                "required_physics_assumption",
                "failure_mode_if_unresolved",
                "claim_ceiling",
                "next_bounded_action",
            }
            <= set(row)
            for row in rows
        ),
        "exactly_one_primary_obstruction_selected": len(selected_rows) == 1
        and selected_rows[0]["missing_condition"] == PRIMARY_MISSING_CONDITION,
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
        else "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_OBSTRUCTION_REFINEMENT_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_statement_witness_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_covariant_conservation_statement_witness_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "accepted_obstruction_classification": ACCEPTED_OBSTRUCTION_CLASSIFICATION,
        "missing_condition_menu": REFINEMENT_CANDIDATES,
        "primary_obstruction_id": PRIMARY_OBSTRUCTION_ID,
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_solved": False,
        "refinement_rows": rows,
        "prepares_refinement_only": True,
        "identifies_covariant_conservation_obstruction_more_narrowly": True,
        "covariant_conservation_statement_witness_constructed": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "qft_gr_seam_closed": False,
        "semiclassical_einstein_equation_derived": False,
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
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_OBSTRUCTION_REFINEMENT_PACKET",
        "selected_next_target_kind": "qft_gr_covariant_derivative_operator_domain_packet_preparation",
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet refines the accepted covariant-conservation statement "
            "obstruction by selecting the missing covariant derivative/operator "
            "domain as the primary blocker. It does not solve the obstruction, "
            "construct a conservation witness, claim Bianchi compatibility, "
            "derive the semiclassical Einstein equation, close QFT-GR, "
            "validate empirically, promote the master action, assemble release, "
            "or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_statement_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_covariant_conservation_statement_obstruction_refinement_packet(
            result_review_path=result_review_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation statement obstruction refinement packet."
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
    payload = write_qft_gr_covariant_conservation_statement_obstruction_refinement_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_statement_obstruction_refinement_packet_report: "
        f"prepared={payload['prepared']} primary={payload['primary_missing_condition']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
