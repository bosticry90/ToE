from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_stress_energy_conservation_obstruction_refinement_packet_report import (
    DEFAULT_OUT as DEFAULT_REFINEMENT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_REFINEMENT_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_REFINEMENT_CLASSIFICATION,
    PACKET_ID as EXPECTED_REFINEMENT_PACKET_ID,
    PRIMARY_MISSING_CONDITION,
    SCHEMA_ID as EXPECTED_REFINEMENT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_stress_energy_conservation_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_v0"
OUTCOME_ID = "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_statement_witness_packet_prepared_"
    "no_witness_construction_no_source_admissibility_or_bianchi_claim"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
POST_PACKET_REVIEW_TARGET = (
    "review_qft_gr_covariant_conservation_statement_witness_packet_result"
)
FUTURE_EXECUTION_TARGET = (
    "execute_qft_gr_covariant_conservation_statement_witness_attempt"
)
FUTURE_EXECUTION_CLASSIFICATIONS = [
    "qft_gr_covariant_conservation_statement_witness_constructed_pending_result_review",
    "qft_gr_covariant_conservation_statement_obstruction_identified_requires_refinement",
    "qft_gr_covariant_conservation_statement_inconclusive_requires_assumption_reduction",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_20260525_v0.json"
)

REQUIRED_PACKET_FIELDS = [
    "candidate_stress_energy_source",
    "renormalization_scope",
    "state_expectation_scope",
    "conservation_form",
    "covariant_derivative_operator",
    "domain_of_validity",
    "required_Bianchi_compatibility_link",
    "required_source_admissibility_link",
    "current_obstruction",
    "required_future_proof_object",
    "required_Lean_surface",
    "required_physics_assumptions",
    "failure_modes",
    "claim_ceiling",
    "forbidden_claims",
    "post_packet_review_target",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _packet_fields() -> dict[str, Any]:
    return {
        "candidate_stress_energy_source": (
            "candidate_renormalized_qft_stress_energy_expectation_source"
        ),
        "renormalization_scope": (
            "bounded renormalization scope inherited from the obstruction "
            "refinement packet; no global renormalization theorem is claimed"
        ),
        "state_expectation_scope": (
            "bounded state class where the renormalized expectation and the "
            "selected covariant-divergence statement can both be meaningful"
        ),
        "conservation_form": (
            "covariant_divergence_zero_statement_for_candidate_renormalized_"
            "stress_energy_source"
        ),
        "covariant_derivative_operator": (
            "repo-local covariant derivative/divergence operator must be "
            "selected or supplied for the bounded domain"
        ),
        "domain_of_validity": (
            "explicit bounded domain where the candidate source, state "
            "expectation, renormalization scope, and covariant derivative "
            "semantics are simultaneously meaningful"
        ),
        "required_Bianchi_compatibility_link": (
            "downstream dependency only; Bianchi compatibility is not claimed "
            "by packet preparation"
        ),
        "required_source_admissibility_link": (
            "downstream dependency only; classical GR-source admissibility is "
            "not claimed by packet preparation"
        ),
        "current_obstruction": PRIMARY_MISSING_CONDITION,
        "required_future_proof_object": (
            "bounded witness statement that the covariant divergence of the "
            "candidate renormalized stress-energy source vanishes on the "
            "selected domain"
        ),
        "required_Lean_surface": [
            "ToeFormal.Bridges.QFT_GR_StressEnergyConservationObstructionRefinementPacket",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
            "ToeFormal.Bridges.QFT_GR_CovariantConservationStatementWitnessPacket",
            "ToeFormal.Release.V01Index",
            "ToeFormal.Derivation.CrossPillarClosureFrontier",
        ],
        "required_physics_assumptions": [
            "renormalized stress-energy expectation is meaningful on the selected state/domain scope",
            "a compatible connection/covariant derivative operator is selected for the background regime",
            "the candidate source admits a tensorial interpretation on the bounded domain",
            "any Ward/conservation identity needed for the statement is explicitly scoped",
        ],
        "failure_modes": [
            "missing_covariant_derivative_operator",
            "renormalized_expectation_domain_mismatch",
            "weak_vs_strong_conservation_form_ambiguity",
            "state_domain_too_broad_for_conservation_identity",
            "Bianchi_link_not_derivable_from_statement_preparation",
            "source_admissibility_still_conditional",
        ],
        "claim_ceiling": (
            "packet_preparation_only_no_covariant_conservation_witness_no_"
            "source_admissibility_no_bianchi_compatibility_no_qft_gr_closure"
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


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": POST_PACKET_REVIEW_TARGET,
            "decision": "selected",
            "reason": "Packet preparation must be result-reviewed before any bounded witness attempt.",
        },
        {
            "target": FUTURE_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Execution requires packet result-review acceptance first.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Domain refinement may follow if the statement packet review exposes a domain blocker.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Covariant-conservation statement packet preparation does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is outside this scientific witness packet.",
        },
    ]


def build_qft_gr_covariant_conservation_statement_witness_packet(
    *,
    refinement_packet_path: Path = DEFAULT_REFINEMENT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    refinement_packet = _read_json(refinement_packet_path)
    packet_fields = _packet_fields()
    candidate_next_targets = _candidate_next_targets()
    nonclaim_flags = {
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
    }
    acceptance_criteria = {
        "consumes_expected_refinement_packet": refinement_packet.get("packet_id")
        == EXPECTED_REFINEMENT_PACKET_ID,
        "refinement_schema_expected": refinement_packet.get("schema_id")
        == EXPECTED_REFINEMENT_SCHEMA_ID,
        "refinement_outcome_expected": refinement_packet.get("outcome_id")
        == EXPECTED_REFINEMENT_OUTCOME,
        "refinement_classification_expected": refinement_packet.get(
            "packet_classification"
        )
        == EXPECTED_REFINEMENT_CLASSIFICATION,
        "refinement_selected_this_packet": refinement_packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "primary_blocker_preserved": refinement_packet.get("primary_missing_condition")
        == PRIMARY_MISSING_CONDITION,
        "required_fields_present": set(REQUIRED_PACKET_FIELDS)
        == set(packet_fields.keys()),
        "prepares_packet_only": all(value is False for value in nonclaim_flags.values()),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == POST_PACKET_REVIEW_TARGET,
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
        else "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_stress_energy_conservation_obstruction_refinement_packet": EXPECTED_REFINEMENT_PACKET_ID,
        "consumes_qft_gr_stress_energy_conservation_obstruction_refinement_packet_pointer": _ptr(
            refinement_packet_path
        ),
        "primary_blocker": PRIMARY_MISSING_CONDITION,
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "packet_question": (
            "Can the repo define a bounded witness statement showing that the "
            "candidate renormalized QFT stress-energy source satisfies the "
            "required covariant conservation condition?"
        ),
        "packet_fields": packet_fields,
        "required_packet_fields": REQUIRED_PACKET_FIELDS,
        "future_execution_classifications": FUTURE_EXECUTION_CLASSIFICATIONS,
        **nonclaim_flags,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": POST_PACKET_REVIEW_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_statement_witness_packet_result_review"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITNESS_PACKET_RESULT_ONLY_"
            "NO_WITNESS_EXECUTION_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares a bounded covariant-conservation statement "
            "witness target for the candidate renormalized QFT stress-energy "
            "source. It does not construct the witness, claim source "
            "admissibility or Bianchi compatibility, derive the semiclassical "
            "Einstein equation, close QFT-GR, validate empirically, promote "
            "the master action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_statement_witness_packet(
    *,
    refinement_packet_path: Path = DEFAULT_REFINEMENT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_statement_witness_packet(
        refinement_packet_path=refinement_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation statement witness packet."
    )
    parser.add_argument(
        "--refinement-packet", type=Path, default=DEFAULT_REFINEMENT_PACKET_PATH
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    refinement_packet_path = (
        ns.refinement_packet
        if ns.refinement_packet.is_absolute()
        else (REPO_ROOT / ns.refinement_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_statement_witness_packet(
        refinement_packet_path=refinement_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_statement_witness_packet_report: "
        f"prepared={payload['prepared']} primary={payload['primary_blocker']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
