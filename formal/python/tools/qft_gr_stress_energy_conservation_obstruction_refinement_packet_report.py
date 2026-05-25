from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_stress_energy_conservation_witness_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OBSTRUCTION_CLASS as ACCEPTED_OBSTRUCTION_CLASSIFICATION,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REFINEMENT_CANDIDATES,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_stress_energy_conservation_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_v0"
OUTCOME_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
PACKET_CLASSIFICATION = (
    "qft_gr_stress_energy_conservation_obstruction_refinement_packet_prepared_"
    "primary_missing_covariant_conservation_statement_no_closure_or_empirical_validation"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "prepare_qft_gr_covariant_conservation_statement_witness_packet"
PRIMARY_OBSTRUCTION_ID = "qft_gr_stress_energy_conservation_missing_covariant_conservation_statement_v0"
PRIMARY_MISSING_CONDITION = "missing_covariant_conservation_statement"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_20260525_v0.json"
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
            "covariant or weak divergence-zero statement is not yet formalized as a witness object",
            "attempt finding: no repo-local witness object proves covariant-divergence-zero or weak-divergence-zero for the candidate renormalized stress-energy expectation",
            "bounded covariant-conservation statement witness for the candidate renormalized stress-energy expectation",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
            "a selected connection/divergence operator and state/domain scope make the conservation statement meaningful",
            "conservation remains unstated as a proof target, so no conservation witness can be constructed",
            NEXT_TARGET,
        ),
        (
            "qft_gr_stress_energy_conservation_weak_strong_ambiguity_v0",
            "weak_vs_strong_conservation_ambiguity",
            "weak and covariant conservation forms are both mentioned but not separated into a selected form",
            "packet field `covariant_or_weak_conservation_form` permits either form",
            "bounded form-selection packet distinguishing strong covariant divergence from weak/test-function conservation",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
            "the selected source domain admits the chosen conservation form",
            "ambiguity prevents checking whether a later proof object satisfies the intended obligation",
            "deferred until the covariant statement packet chooses the statement form",
        ),
        (
            "qft_gr_stress_energy_conservation_renormalized_expectation_domain_v0",
            "renormalized_expectation_not_yet_well_defined_enough",
            "renormalized expectation semantics remain prerequisite surfaces rather than a conservation-domain theorem",
            "renormalized expectation and state-expectation semantics surfaces",
            "domain adequacy witness tying the renormalized expectation to the conservation operator",
            "ToeFormal.Bridges.QFT_GR_RenormalizedExpectationValueSemantics",
            "renormalized stress-energy expectation is defined on the same domain used by the conservation statement",
            "the conservation operator may not apply to the candidate expectation",
            "deferred as a likely follow-on if the statement packet cannot bind the domain",
        ),
        (
            "qft_gr_stress_energy_conservation_state_domain_limitation_v0",
            "state_domain_limitation",
            "state class/domain assumptions are not narrow enough to support a conservation witness",
            "state-expectation scope in the conservation witness packet",
            "bounded state-domain restriction sufficient for conservation",
            "ToeFormal.Bridges.QFT_GR_StateExpectationFunctionalSemantics",
            "selected state class preserves the Ward/conservation identity required by the source",
            "the conservation claim remains too broad for the available assumptions",
            "deferred pending covariant statement and domain review",
        ),
        (
            "qft_gr_stress_energy_conservation_bianchi_dependency_v0",
            "Bianchi_compatibility_not_derivable_from_current_assumptions",
            "Bianchi compatibility remains downstream and cannot be inferred from the obstruction review",
            "Bianchi-compatibility obligation semantics surface",
            "bounded Bianchi dependency map after conservation statement/refinement",
            "ToeFormal.Bridges.QFT_GR_BianchiCompatibilityObligationSemantics",
            "accepted conservation statement can be related to the contracted Bianchi identity boundary",
            "Bianchi compatibility cannot be claimed from conservation packet preparation alone",
            "deferred; no Bianchi compatibility claim authorized",
        ),
        (
            "qft_gr_stress_energy_conservation_classical_source_conditional_v0",
            "classical_source_admissibility_still_conditional",
            "classical GR-source admissibility remains conditional on conservation and Bianchi boundaries",
            "classical-source admissibility semantics surface",
            "bounded source-admissibility witness after conservation and Bianchi review",
            "ToeFormal.Bridges.QFT_GR_ClassicalSourceAdmissibilitySemantics",
            "renormalized expectation can be treated as a classical tensor source in the bounded regime",
            "stress-energy source admissibility remains unclaimed",
            "deferred; no source-admissibility claim authorized",
        ),
    ]
    return [
        {
            "obstruction_id": row[0],
            "missing_condition": row[1],
            "conservation_form_required": row[2],
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
            "reason": "The primary blocker is the missing covariant conservation statement witness.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Domain conservation may be needed after the conservation statement packet.",
        },
        {
            "target": "prepare_qft_gr_stress_energy_conservation_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Assumption reduction is not selected before the statement witness packet.",
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


def build_qft_gr_stress_energy_conservation_obstruction_refinement_packet(
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
                "conservation_form_required",
                "available_repo_evidence",
                "missing_condition",
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
        else "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_stress_energy_conservation_witness_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_stress_energy_conservation_witness_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "accepted_obstruction_classification": ACCEPTED_OBSTRUCTION_CLASSIFICATION,
        "missing_condition_menu": REFINEMENT_CANDIDATES,
        "primary_obstruction_id": PRIMARY_OBSTRUCTION_ID,
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_solved": False,
        "refinement_rows": rows,
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
        else "REMEDIATE_QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET",
        "selected_next_target_kind": "qft_gr_covariant_conservation_statement_witness_packet_preparation",
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet refines the accepted conservation obstruction by "
            "selecting the missing covariant conservation statement as the "
            "primary blocker. It does not solve the obstruction, construct a "
            "conservation witness, claim Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_stress_energy_conservation_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_stress_energy_conservation_obstruction_refinement_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR stress-energy conservation obstruction refinement packet."
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
    payload = write_qft_gr_stress_energy_conservation_obstruction_refinement_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_stress_energy_conservation_obstruction_refinement_packet_report: "
        f"prepared={payload['prepared']} primary={payload['primary_missing_condition']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
