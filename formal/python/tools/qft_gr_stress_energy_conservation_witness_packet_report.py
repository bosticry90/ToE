from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as ACCEPTED_RESULT_REVIEW_OUTCOME,
    PRIMARY_MISSING_CONDITION,
    RESULT_REVIEW_CLASSIFICATION as ACCEPTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as ACCEPTED_RESULT_REVIEW_ID,
    SCHEMA_ID as ACCEPTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-05-25T00:00:00Z"
SCHEMA_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_PREPARED_WITH_NO_"
    "QFT_GR_SEAM_CLOSURE_OR_MASTER_ACTION_PROMOTION"
)
# Full token retained for substring gates:
# QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_MASTER_ACTION_PROMOTION
PACKET_CLASSIFICATION = (
    "qft_gr_stress_energy_conservation_witness_packet_prepared_no_witness_"
    "construction_no_source_admissibility_or_seam_closure"
)
CONSUMED_TARGET = "prepare_qft_gr_stress_energy_conservation_witness_packet"
POST_PACKET_REVIEW_TARGET = "review_qft_gr_stress_energy_conservation_witness_packet_result"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def build_qft_gr_stress_energy_conservation_witness_packet(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    required_packet_fields = {
        "source_object": "candidate_renormalized_qft_stress_energy_source",
        "renormalization_scope": (
            "bounded renormalized expectation scope inherited from the QFT-GR "
            "source witness lane; no global renormalization theorem is claimed"
        ),
        "state_expectation_scope": (
            "state expectation semantics already required by the conserved "
            "renormalized source witness packet; conservation is the only "
            "primary obstruction targeted here"
        ),
        "conservation_statement": (
            "the candidate renormalized stress-energy source should satisfy the "
            "conservation condition required for GR-source admissibility"
        ),
        "covariant_or_weak_conservation_form": (
            "bounded covariant-conservation or weak-divergence-zero witness, "
            "depending on the available repo surface"
        ),
        "domain_of_validity": (
            "explicit bounded domain/regime where renormalization, expectation, "
            "and source semantics are all available as assumptions or surfaces"
        ),
        "Bianchi_compatibility_dependency": (
            "Bianchi compatibility remains downstream and is not claimed by this "
            "packet"
        ),
        "required_Lean_surfaces": [
            "ToeFormal.Bridges.QFT_GR_ConservedRenormalizedStressEnergySourceWitnessObstructionRefinementPacketResultReview",
            "ToeFormal.Bridges.QFT_GR_StressEnergyConservationWitnessPacket",
            "ToeFormal.Release.V01Index",
            "ToeFormal.Derivation.CrossPillarClosureFrontier",
        ],
        "required_math_assumptions": [
            "well-formed divergence or weak-divergence operator on the bounded source domain",
            "compatibility between the selected conservation form and the source object",
            "domain restrictions sufficient to state conservation without proving global QFT existence",
        ],
        "required_physics_assumptions": [
            "renormalized stress-energy expectation is meaningful on the bounded domain",
            "state/renormalization choices do not violate the selected conservation form",
            "GR-source admissibility requires conservation before Bianchi compatibility can be reviewed",
        ],
        "failure_modes": [
            "renormalization scope too weak to state conservation",
            "state expectation semantics insufficient for a conserved source statement",
            "covariant conservation form unavailable",
            "weak conservation form unavailable or not tied to GR-source admissibility",
            "Bianchi compatibility dependency cannot be deferred cleanly",
            "Lean surfaces cannot express the required conservation witness object",
        ],
        "claim_ceiling": (
            "prepares a conservation-witness attempt only; no witness, "
            "source-admissibility, Bianchi compatibility, semiclassical Einstein "
            "equation, QFT-GR seam closure, empirical validation, master-action "
            "promotion, release assembly, or public submission is claimed"
        ),
        "forbidden_claims": [
            "conservation_witness_constructed",
            "stress_energy_source_admissibility_claimed",
            "Bianchi_compatibility_claimed",
            "semiclassical_einstein_equation_derived",
            "qft_gr_seam_closed",
            "empirical_validation_claimed",
            "master_action_promoted",
            "release_assembly_authorized",
            "public_submission_authorized",
        ],
        "post_packet_review_target": POST_PACKET_REVIEW_TARGET,
    }
    acceptance_criteria = {
        "consumes_obstruction_refinement_result_review": result_review.get("review_id")
        == ACCEPTED_RESULT_REVIEW_ID
        and result_review.get("schema_id") == ACCEPTED_RESULT_REVIEW_SCHEMA_ID,
        "accepted_result_review_outcome": result_review.get("outcome_id")
        == ACCEPTED_RESULT_REVIEW_OUTCOME,
        "accepted_result_review_classification": result_review.get(
            "result_review_classification"
        )
        == ACCEPTED_RESULT_REVIEW_CLASSIFICATION,
        "primary_obstruction_is_conservation": result_review.get(
            "primary_missing_condition"
        )
        == PRIMARY_MISSING_CONDITION
        and result_review.get("conservation_primary_obstruction_accepted") is True,
        "required_fields_present": set(required_packet_fields)
        == {
            "source_object",
            "renormalization_scope",
            "state_expectation_scope",
            "conservation_statement",
            "covariant_or_weak_conservation_form",
            "domain_of_validity",
            "Bianchi_compatibility_dependency",
            "required_Lean_surfaces",
            "required_math_assumptions",
            "required_physics_assumptions",
            "failure_modes",
            "claim_ceiling",
            "forbidden_claims",
            "post_packet_review_target",
        },
        "exactly_one_next_target_selected": POST_PACKET_REVIEW_TARGET
        == "review_qft_gr_stress_energy_conservation_witness_packet_result",
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
        else "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review": ACCEPTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_preserved": True,
        "packet_question": (
            "Can the repo define a bounded witness that the candidate "
            "renormalized QFT stress-energy source satisfies the conservation "
            "condition needed for GR-source admissibility?"
        ),
        **required_packet_fields,
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
        "candidate_next_targets": [
            {
                "target": POST_PACKET_REVIEW_TARGET,
                "decision": "selected",
                "reason": "Packet preparation must be reviewed before a conservation witness attempt is authorized.",
            },
            {
                "target": "execute_qft_gr_stress_energy_conservation_witness_attempt",
                "decision": "deferred",
                "reason": "Execution requires packet result review acceptance first.",
            },
            {
                "target": "close_qft_gr_seam",
                "decision": "not_authorized",
                "reason": "Packet preparation does not close QFT-GR.",
            },
        ],
        "selected_next_target": POST_PACKET_REVIEW_TARGET if prepared else "REMEDIATE_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET",
        "selected_next_target_kind": "qft_gr_stress_energy_conservation_witness_packet_result_review",
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_ONLY_"
            "NO_WITNESS_EXECUTION_OR_SEAM_CLOSURE"
        ),
        "future_execution_classifications": [
            "qft_gr_stress_energy_conservation_witness_constructed_pending_result_review",
            "qft_gr_stress_energy_conservation_obstruction_identified_requires_refinement",
            "qft_gr_stress_energy_conservation_inconclusive_requires_assumption_reduction",
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only a bounded conservation-witness attempt. "
            "It does not construct the conservation witness, claim stress-energy "
            "source admissibility or Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate empirically, "
            "promote the master action, assemble release, or authorize public "
            "submission."
        ),
    }


def write_qft_gr_stress_energy_conservation_witness_packet(
    *,
    result_review_path: Path = RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_stress_energy_conservation_witness_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR stress-energy conservation witness packet."
    )
    parser.add_argument("--result-review", type=Path, default=RESULT_REVIEW_PATH)
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
    payload = write_qft_gr_stress_energy_conservation_witness_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_stress_energy_conservation_witness_packet_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
