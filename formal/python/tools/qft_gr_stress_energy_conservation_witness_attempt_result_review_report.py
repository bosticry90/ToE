from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_stress_energy_conservation_witness_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_RESULT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_stress_energy_conservation_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_RESULT_REVIEW_20260525_v0"
)
REVIEW_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_RESULT_REVIEW_v0"
OUTCOME_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_RESULT_REVIEW_ACCEPTS_CONSERVATION_OBSTRUCTION_AND_AUTHORIZES_REFINEMENT_PACKET_PREPARATION_ONLY"
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_stress_energy_conservation_witness_attempt_result_review_accepts_"
    "conservation_obstruction_and_authorizes_refinement_packet_preparation_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = "prepare_qft_gr_stress_energy_conservation_obstruction_refinement_packet"
OBSTRUCTION_CLASS = EXPECTED_RESULT_CLASSIFICATION

REFINEMENT_CANDIDATES = [
    "missing_covariant_conservation_statement",
    "weak_vs_strong_conservation_ambiguity",
    "renormalized_expectation_not_yet_well_defined_enough",
    "state_domain_limitation",
    "Bianchi_compatibility_not_derivable_from_current_assumptions",
    "classical_source_admissibility_still_conditional",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_RESULT_REVIEW_20260525_v0.json"
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
            "reason": "Accepted conservation obstruction requires a bounded refinement packet before further execution.",
        },
        {
            "target": "execute_qft_gr_stress_energy_conservation_refinement_attempt",
            "decision": "deferred",
            "reason": "Execution requires a later refinement packet result review.",
        },
        {
            "target": "prepare_qft_gr_stress_energy_conservation_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Assumption reduction is not selected while refinement packet preparation is accepted.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Conservation obstruction acceptance does not close the QFT-GR seam.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this result review.",
        },
    ]


def build_qft_gr_stress_energy_conservation_witness_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "consumes_expected_attempt": attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID,
        "attempt_schema_expected": attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID,
        "attempt_outcome_expected": attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_selected_this_review": attempt.get("selected_next_target")
        == CONSUMED_TARGET,
        "classification_is_conservation_obstruction": attempt.get(
            "result_classification"
        )
        == EXPECTED_RESULT_CLASSIFICATION,
        "exactly_one_result_classification": attempt.get("result_classification_count")
        == 1,
        "no_conservation_witness_constructed": attempt.get(
            "conservation_witness_constructed"
        )
        is False
        and attempt.get("constructed_witness_result") is False,
        "no_source_or_bianchi_claim": attempt.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and attempt.get("Bianchi_compatibility_claimed") is False,
        "no_qft_gr_closure_or_einstein_derivation": attempt.get("qft_gr_seam_closed")
        is False
        and attempt.get("semiclassical_einstein_equation_derived") is False,
        "no_empirical_master_release_or_public_submission": attempt.get(
            "empirical_validation_claimed"
        )
        is False
        and attempt.get("master_action_promoted") is False
        and attempt.get("release_assembly_authorized") is False
        and attempt.get("public_submission_authorized") is False,
        "conservation_obstruction_class_recorded": attempt.get(
            "obstruction_identified_result"
        )
        is True
        and attempt.get("primary_missing_condition") == "conservation",
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
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_stress_energy_conservation_witness_attempt": EXPECTED_ATTEMPT_ID,
        "consumes_qft_gr_stress_energy_conservation_witness_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "attempt_result_reviewed": accepted,
        "conservation_obstruction_result_accepted": accepted,
        "obstruction_class": OBSTRUCTION_CLASS,
        "primary_missing_condition": "conservation",
        "refinement_packet_preparation_authorized": accepted,
        "refinement_candidates": REFINEMENT_CANDIDATES,
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
        if accepted
        else "REMEDIATE_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_RESULT_REVIEW",
        "selected_next_target_kind": (
            "qft_gr_stress_energy_conservation_obstruction_refinement_packet_preparation_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_"
            "PACKET_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the bounded conservation obstruction and "
            "authorizes only refinement packet preparation. It does not construct "
            "a conservation witness, claim stress-energy source admissibility, "
            "claim Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, promote the master "
            "action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_stress_energy_conservation_witness_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_stress_energy_conservation_witness_attempt_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR stress-energy conservation witness attempt result review."
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_stress_energy_conservation_witness_attempt_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_stress_energy_conservation_witness_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
