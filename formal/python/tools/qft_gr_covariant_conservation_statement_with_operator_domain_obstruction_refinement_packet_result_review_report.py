from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    MISSING_PROOF_OBJECT,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIMARY_MISSING_CONDITION,
    PRIMARY_OBSTRUCTION_ID,
    REQUIRED_ASSUMPTIONS,
    REQUIRED_LEAN_SURFACE,
    REQUIRED_THEOREM_SHAPE,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_"
    "REFINEMENT_PACKET_RESULT_REVIEW_20260525_v0"
)
REVIEW_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_"
    "REFINEMENT_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_"
    "REFINEMENT_RESULT_REVIEW_ACCEPTS_MISSING_CONSERVATION_PROOF_OBJECT_AND_"
    "AUTHORIZES_PROOF_OBJECT_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_"
    "refinement_result_review_accepts_missing_conservation_proof_object_and_"
    "authorizes_proof_object_packet_preparation_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = "prepare_qft_gr_covariant_conservation_proof_object_packet"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_20260525_v0.json"
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
            "reason": "The accepted refined obstruction is the missing conservation proof object, so only proof-object packet preparation is authorized.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt",
            "decision": "deferred",
            "reason": "Execution remains blocked until a proof-object packet is prepared and reviewed.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_conservation_packet",
            "decision": "deferred",
            "reason": "Expectation-domain work remains secondary unless selected after the proof-object packet path.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Result review does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this result review.",
        },
    ]


def build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "selected_obstruction_expected": packet.get("selected_obstruction")
        == PRIMARY_MISSING_CONDITION,
        "missing_proof_object_expected": packet.get("missing_proof_object")
        == MISSING_PROOF_OBJECT,
        "required_theorem_shape_expected": packet.get("required_theorem_shape")
        == REQUIRED_THEOREM_SHAPE,
        "required_assumptions_expected": packet.get("required_assumptions")
        == REQUIRED_ASSUMPTIONS,
        "required_lean_surface_expected": packet.get("required_Lean_surface")
        == REQUIRED_LEAN_SURFACE,
        "no_proof_object_or_witness_constructed": packet.get(
            "primary_obstruction_solved"
        )
        is False
        and packet.get("covariant_conservation_statement_with_operator_domain_witness_constructed")
        is False
        and packet.get("conservation_witness_constructed") is False,
        "no_source_bianchi_einstein_or_seam_claim": packet.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and packet.get("Bianchi_compatibility_claimed") is False
        and packet.get("semiclassical_einstein_equation_derived") is False
        and packet.get("qft_gr_seam_closed") is False,
        "no_empirical_master_release_or_public_submission": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("master_action_promoted") is False
        and packet.get("release_assembly_authorized") is False
        and packet.get("public_submission_authorized") is False,
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
        else "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "obstruction_refinement_packet_result_reviewed": accepted,
        "missing_conservation_proof_object_accepted": accepted,
        "selected_obstruction": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_id": PRIMARY_OBSTRUCTION_ID,
        "missing_proof_object": MISSING_PROOF_OBJECT,
        "required_theorem_shape": REQUIRED_THEOREM_SHAPE,
        "required_assumptions": REQUIRED_ASSUMPTIONS,
        "required_Lean_surface": REQUIRED_LEAN_SURFACE,
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
        "proof_object_packet_preparation_authorized": accepted,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "qft_gr_covariant_conservation_proof_object_packet_preparation",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the missing conservation proof object "
            "as the post-operator-domain obstruction and authorizes only proof "
            "object packet preparation. It does not construct the proof object "
            "or conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR operator-domain obstruction refinement packet result review."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
