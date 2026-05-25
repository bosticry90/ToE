from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_attempt_report import (
    RESULT_CLASSIFICATION as ACCEPTED_OBSTRUCTION_CLASSIFICATION,
)
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    MISSING_CONDITION_CANDIDATES,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    OBSTRUCTION_CLASS,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_20260525_v0"
)
PACKET_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_v0"
)
OUTCOME_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_PREPARED_WITH_NO_SEAM_CLOSURE_OR_"
    "EMPIRICAL_VALIDATION"
)
PACKET_CLASSIFICATION = (
    "qft_gr_conserved_renormalized_source_witness_obstruction_refinement_"
    "packet_prepared_primary_conservation_obstruction_no_closure_or_empirical_"
    "validation"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "prepare_qft_gr_stress_energy_conservation_witness_packet"
PRIMARY_OBSTRUCTION_ID = "qft_gr_primary_obstruction_covariant_conservation_v0"
PRIMARY_MISSING_CONDITION = "conservation"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _refinement_rows() -> list[dict[str, Any]]:
    rows = [
        (
            "qft_gr_obstruction_finiteness_v0",
            "finiteness",
            "candidate expectation finiteness not discharged",
            "renormalized-expectation semantics surface states the obligation",
            "bounded finiteness witness for <T_mu_nu>_ren in the declared scope",
            "renormalization prescription supplies finite expectation values for the selected state class",
            "ToeFormal.Bridges.QFT_GR_RenormalizedExpectationValueSemantics",
            "without finiteness, conservation and source admissibility cannot be meaningful source claims",
            "not selected as primary before conservation witness packet",
        ),
        (
            "qft_gr_obstruction_renormalization_scope_v0",
            "renormalization_scope",
            "scope is declared but not promoted to a solved scheme",
            "renormalization-scope packet fields and expectation-value semantics",
            "bounded renormalization-scope adequacy witness",
            "selected renormalization scope is physically meaningful for the target state class",
            "ToeFormal.Bridges.QFT_GR_RenormalizedExpectationValueSemantics",
            "without scope adequacy, finiteness and conservation evidence remain scheme-relative",
            "not selected as primary before conservation witness packet",
        ),
        (
            "qft_gr_obstruction_state_expectation_meaning_v0",
            "state_expectation_meaning",
            "state expectation semantics are prerequisites, not a completed witness",
            "state-expectation functional semantics surface",
            "bounded state-expectation meaningfulness witness",
            "state class admits the declared renormalized stress-energy expectation",
            "ToeFormal.Bridges.QFT_GR_StateExpectationFunctionalSemantics",
            "without meaning, the stress-energy object is not an admissible witness candidate",
            "not selected as primary before conservation witness packet",
        ),
        (
            PRIMARY_OBSTRUCTION_ID,
            PRIMARY_MISSING_CONDITION,
            "primary obstruction selected; covariant conservation is not discharged for <T_mu_nu>_ren",
            "covariant-conservation obligation semantics plus attempt obstruction findings",
            "bounded covariant-conservation witness for the renormalized stress-energy expectation",
            "renormalized expectation lies in a state/scope where covariant divergence is meaningful and can vanish",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
            "without conservation, Bianchi compatibility and classical GR source admissibility remain blocked",
            NEXT_TARGET,
        ),
        (
            "qft_gr_obstruction_bianchi_compatibility_v0",
            "Bianchi_compatibility",
            "depends on conservation and remains unclosed",
            "Bianchi-compatibility obligation semantics surface",
            "bounded Bianchi-compatibility witness after conservation evidence",
            "candidate source can satisfy the Bianchi boundary for Einstein coupling",
            "ToeFormal.Bridges.QFT_GR_BianchiCompatibilityObligationSemantics",
            "without Bianchi compatibility, Einstein coupling cannot be interpreted as a GR source bridge",
            "deferred until conservation witness packet is reviewed",
        ),
        (
            "qft_gr_obstruction_classical_source_admissibility_v0",
            "classical_source_admissibility",
            "classical admissibility remains unclaimed",
            "classical-source admissibility semantics surface",
            "bounded classical-source admissibility witness",
            "renormalized expectation is admissible as a classical tensor source in the target regime",
            "ToeFormal.Bridges.QFT_GR_ClassicalSourceAdmissibilitySemantics",
            "without admissibility, the candidate cannot serve as the GR source object",
            "deferred until conservation and Bianchi boundaries are review-accepted",
        ),
        (
            "qft_gr_obstruction_einstein_coupling_boundary_v0",
            "Einstein_coupling_boundary",
            "coupling remains only a boundary check",
            "Einstein-coupling obligation semantics surface",
            "bounded Einstein-coupling boundary witness after source admissibility",
            "semiclassical coupling boundary is meaningful without deriving the full equation",
            "ToeFormal.Bridges.QFT_GR_EinsteinCouplingObligationSemantics",
            "without this boundary, source admissibility cannot be connected to Einstein-side interpretation",
            "deferred; no semiclassical Einstein equation derivation authorized",
        ),
        (
            "qft_gr_obstruction_weak_curvature_poisson_recovery_v0",
            "weak_curvature_or_Poisson_recovery",
            "recovery remains only a boundary check",
            "weak-curvature and Poisson-recovery obligation semantics surfaces",
            "bounded recovery-boundary witness after source admissibility",
            "target regime admits a weak-curvature or Poisson comparison map",
            "ToeFormal.Bridges.QFT_GR_PoissonRecoveryObligationSemantics",
            "without recovery evidence, the candidate lacks this limited regime check",
            "deferred; no empirical validation authorized",
        ),
    ]
    return [
        {
            "obstruction_id": row[0],
            "missing_condition": row[1],
            "current_status": row[2],
            "available_repo_evidence": row[3],
            "required_future_proof_object": row[4],
            "required_physics_assumption": row[5],
            "required_Lean_surface": row[6],
            "failure_mode_if_unresolved": row[7],
            "claim_ceiling": "obstruction_refinement_packet_only_no_witness_construction_no_qft_gr_closure",
            "next_bounded_action": row[8],
        }
        for row in rows
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "Conservation is the primary obstruction before Bianchi compatibility and GR source admissibility can be tested.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_finiteness_witness_packet",
            "decision": "deferred",
            "reason": "Finiteness remains on the menu but is not selected as the first bottleneck in this packet.",
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_witness_packet",
            "decision": "deferred",
            "reason": "Bianchi compatibility depends on conservation evidence.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Refinement packet preparation does not close the QFT-GR seam.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this refinement packet.",
        },
    ]


def build_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet(
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
        == ACCEPTED_OBSTRUCTION_CLASSIFICATION
        == OBSTRUCTION_CLASS,
        "full_missing_condition_menu_preserved": review.get(
            "missing_condition_candidates_for_refinement_packet"
        )
        == MISSING_CONDITION_CANDIDATES,
        "row_structure_complete": all(
            {
                "obstruction_id",
                "missing_condition",
                "current_status",
                "available_repo_evidence",
                "required_future_proof_object",
                "required_physics_assumption",
                "required_Lean_surface",
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
        else "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_OBSTRUCTION_REFINEMENT_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "accepted_obstruction_classification": ACCEPTED_OBSTRUCTION_CLASSIFICATION,
        "missing_condition_menu": MISSING_CONDITION_CANDIDATES,
        "primary_obstruction_id": PRIMARY_OBSTRUCTION_ID,
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_solved": False,
        "refinement_rows": rows,
        "witness_constructed": False,
        "completed_witness_constructed": False,
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
        else "REMEDIATE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_OBSTRUCTION_REFINEMENT_PACKET",
        "selected_next_target_kind": "qft_gr_stress_energy_conservation_witness_packet_preparation",
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_ONLY_"
            "NO_WITNESS_CONSTRUCTION_OR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet refines the accepted QFT-GR witness obstruction by "
            "selecting conservation as the primary missing condition and "
            "authorizing only a conservation witness packet. It does not solve "
            "the obstruction, construct a conserved renormalized source, derive "
            "the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR conserved renormalized stress-energy source witness obstruction refinement packet."
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
    payload = write_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_report: "
        f"prepared={payload['prepared']} primary={payload['primary_missing_condition']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
