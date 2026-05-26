from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_proof_object_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PROOF_OBJECT_OBSTRUCTION_CLASS,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_packet_report import (
    COVARIANT_CONSERVATION_STATEMENT,
    SELECTED_OBSTRUCTION,
    TARGET_PROOF_OBJECT,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_"
    "20260525_v0"
)
PACKET_ID = "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_"
    "PREPARED_WITH_NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
)
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_"
    "prepared_primary_insufficient_assumptions_for_conservation_no_closure_or_"
    "empirical_validation"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
PRIMARY_BLOCKER = "insufficient_assumptions_for_conservation"
NEXT_TARGET = (
    "review_qft_gr_covariant_conservation_proof_object_obstruction_refinement_"
    "packet_result"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _blocker_menu() -> list[str]:
    return [
        "missing_theorem_shape",
        PRIMARY_BLOCKER,
        "operator_domain_still_too_weak",
        "renormalized_expectation_not_compatible_with_derivative_action",
        "state_domain_limitation",
        "weak_strong_conservation_mismatch",
        "Bianchi_compatibility_dependency_still_unresolved",
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The proof-object obstruction refinement packet must be reviewed before any narrower proof-object or assumption-reduction work is authorized.",
        },
        {
            "target": "prepare_qft_gr_covariant_conservation_assumptions_packet",
            "decision": "deferred",
            "reason": "Assumption refinement is plausible but requires acceptance of this obstruction-refinement packet.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "deferred",
            "reason": "A new proof-object attempt remains unauthorized until the blocker refinement is reviewed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "A narrowed proof-object obstruction does not close the QFT-GR seam.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by obstruction refinement.",
        },
    ]


def build_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    blocker_menu = _blocker_menu()
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "consumes_expected_attempt_result_review": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_proof_object_obstruction_class": result_review.get(
            "proof_object_obstruction_class"
        )
        == PROOF_OBJECT_OBSTRUCTION_CLASS,
        "refines_to_one_primary_blocker": PRIMARY_BLOCKER in blocker_menu,
        "does_not_construct_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed_pending_result_review")
        is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_source_or_bianchi": result_review.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and result_review.get("Bianchi_compatibility_claimed") is False,
        "does_not_close_or_validate": result_review.get("qft_gr_seam_closed")
        is False
        and result_review.get("empirical_validation_claimed") is False,
        "no_release_or_public_submission": result_review.get(
            "release_assembly_authorized"
        )
        is False
        and result_review.get("public_submission_authorized") is False,
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
        else "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_proof_object_attempt_result_review": EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "consumes_qft_gr_covariant_conservation_proof_object_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_id": EXPECTED_RESULT_REVIEW_ID,
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "proof_object_obstruction_class": PROOF_OBJECT_OBSTRUCTION_CLASS,
        "selected_obstruction": SELECTED_OBSTRUCTION,
        "target_proof_object": TARGET_PROOF_OBJECT,
        "covariant_conservation_statement_to_be_proved": COVARIANT_CONSERVATION_STATEMENT,
        "blocker_menu": blocker_menu,
        "blocker_menu_count": len(blocker_menu),
        "primary_blocker": PRIMARY_BLOCKER,
        "selected_primary_blocker": PRIMARY_BLOCKER,
        "primary_blocker_selection_rationale": (
            "The theorem shape and operator-domain statement have been prepared, "
            "but the repo still lacks explicit assumptions such as a conservation "
            "law, Ward identity, derivative-exchange principle, or state-domain "
            "stability sufficient to prove covariant divergence zero."
        ),
        "available_repo_evidence": [
            "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_v0",
            "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_ATTEMPT_v0",
            EXPECTED_RESULT_REVIEW_ID,
        ],
        "required_future_proof_object": (
            "conservation_proof_object_requires_explicit_conservation_law_or_"
            "Ward_identity_and_derivative_compatibility_assumptions"
        ),
        "required_assumption_refinement": (
            "bounded assumptions tying the candidate source, renormalized "
            "expectation, state domain, derivative action, and weak/strong "
            "conservation form to covariant divergence zero"
        ),
        "required_Lean_surface": (
            "ToeFormal.Bridges.QFT_GR_CovariantConservationProofObjectAttempt"
        ),
        "failure_mode_if_unresolved": (
            "without sufficient conservation assumptions, the proof object cannot "
            "be constructed and conservation witness, source admissibility, and "
            "Bianchi-compatible QFT-GR source claims remain blocked"
        ),
        "claim_ceiling": (
            "obstruction_refinement_packet_only_no_proof_object_or_qft_gr_closure"
        ),
        "prepares_refinement_only": True,
        "identifies_proof_object_obstruction_more_narrowly": True,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
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
        if prepared
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_after_packet_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_"
            "REFINEMENT_PACKET_RESULT_ONLY_NO_PROOF_OBJECT_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet refines the proof-object obstruction only. It identifies "
            "insufficient assumptions for conservation as the primary blocker and "
            "does not construct a proof object or conservation witness, claim "
            "source admissibility or Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate empirically, "
            "promote the master action, assemble release, or authorize public "
            "submission."
        ),
    }


def write_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation proof-object obstruction refinement packet."
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
    payload = write_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_report: "
        f"prepared={payload['prepared']} primary={payload['primary_blocker']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
