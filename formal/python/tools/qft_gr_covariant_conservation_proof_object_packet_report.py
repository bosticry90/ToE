from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    MISSING_PROOF_OBJECT,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REQUIRED_ASSUMPTIONS,
    REQUIRED_LEAN_SURFACE,
    REQUIRED_THEOREM_SHAPE,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_proof_object_packet_prepared_no_"
    "conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
SELECTED_OBSTRUCTION = "post_operator_domain_statement_missing_conservation_proof_object"
TARGET_PROOF_OBJECT = MISSING_PROOF_OBJECT
COVARIANT_CONSERVATION_STATEMENT = REQUIRED_THEOREM_SHAPE
NEXT_TARGET = "review_qft_gr_covariant_conservation_proof_object_packet_result"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _failure_modes() -> list[str]:
    return [
        "operator_domain_assumptions_insufficient_for_candidate_source_membership",
        "renormalized_stress_energy_source_assumptions_do_not_stabilize_covariant_divergence",
        "state_expectation_assumptions_do_not_support_derivative_exchange_or_weak_form",
        "weak_strong_conservation_form_mismatch",
        "missing_conservation_law_or_ward_identity_for_selected_source",
        "Bianchi_compatibility_dependency_remains_unavailable_after_proof_object_review",
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The proof-object packet must be reviewed before any proof or witness attempt is authorized.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "deferred",
            "reason": "Execution is not authorized by packet preparation.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt",
            "decision": "deferred",
            "reason": "The broader conservation witness attempt remains blocked until proof-object packet review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Proof-object packet preparation does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this packet.",
        },
    ]


def build_qft_gr_covariant_conservation_proof_object_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    candidate_next_targets = _candidate_next_targets()
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
        "selected_obstruction_expected": review.get("selected_obstruction")
        == SELECTED_OBSTRUCTION,
        "missing_proof_object_expected": review.get("missing_proof_object")
        == TARGET_PROOF_OBJECT,
        "review_constructed_no_proof_or_witness": review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and review.get("conservation_witness_constructed") is False,
        "required_fields_defined": all(
            [
                SELECTED_OBSTRUCTION,
                TARGET_PROOF_OBJECT,
                COVARIANT_CONSERVATION_STATEMENT,
                REQUIRED_ASSUMPTIONS,
                REQUIRED_LEAN_SURFACE,
            ]
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
        else "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_proof_object_refinement_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_covariant_conservation_proof_object_refinement_result_review_pointer": _ptr(
            result_review_path
        ),
        "selected_obstruction": SELECTED_OBSTRUCTION,
        "target_proof_object": TARGET_PROOF_OBJECT,
        "covariant_conservation_statement_to_be_proved": COVARIANT_CONSERVATION_STATEMENT,
        "operator_domain_assumptions": REQUIRED_ASSUMPTIONS,
        "renormalized_stress_energy_source_assumptions": (
            "candidate renormalized stress-energy expectation is the selected "
            "source object and is admitted to the prepared operator domain"
        ),
        "state_expectation_assumptions": (
            "state expectation is meaningful on the selected state domain and "
            "compatible with the conservation statement form"
        ),
        "weak_strong_conservation_form": (
            "bounded form selection required: strong covariant divergence zero "
            "or weak/distributional conservation must be fixed before execution"
        ),
        "Bianchi_compatibility_dependency": (
            "downstream only; Bianchi compatibility may consume an accepted "
            "conservation proof object later but is not claimed here"
        ),
        "required_Lean_surface": REQUIRED_LEAN_SURFACE,
        "required_physics_assumptions": [
            "renormalization prescription supports the selected source object",
            "state-expectation semantics apply on the chosen domain",
            "covariant derivative/divergence operator is the accepted operator-domain structure",
            "any conservation law or Ward-identity premise is explicit and bounded",
        ],
        "failure_modes": _failure_modes(),
        "claim_ceiling": "proof_object_packet_only_no_proof_construction_or_qft_gr_closure",
        "next_bounded_action": NEXT_TARGET,
        "prepares_proof_object_packet_only": True,
        "conservation_proof_object_constructed": False,
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
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET",
        "selected_next_target_kind": "qft_gr_covariant_conservation_proof_object_packet_result_review",
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_RESULT_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet defines the bounded proof-object shape required for a "
            "future conservation attempt. It does not construct the proof "
            "object or conservation witness, claim source admissibility or "
            "Bianchi compatibility, derive the semiclassical Einstein equation, "
            "close QFT-GR, validate empirically, promote the master action, "
            "assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_proof_object_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_proof_object_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation proof-object packet."
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
    payload = write_qft_gr_covariant_conservation_proof_object_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_proof_object_packet_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
