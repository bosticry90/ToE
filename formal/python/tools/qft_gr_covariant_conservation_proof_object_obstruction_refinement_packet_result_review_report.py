from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIMARY_BLOCKER,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_attempt_result_review_report import (
    PROOF_OBJECT_OBSTRUCTION_CLASS,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_"
    "RESULT_REVIEW_20260525_v0"
)
REVIEW_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_RESULT_"
    "REVIEW_ACCEPTS_INSUFFICIENT_ASSUMPTIONS_BLOCKER_AND_AUTHORIZES_ASSUMPTION_"
    "REDUCTION_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_covariant_conservation_proof_object_obstruction_refinement_result_review_"
    "accepts_insufficient_assumptions_blocker_and_authorizes_assumption_reduction_"
    "packet_preparation_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = "prepare_qft_gr_covariant_conservation_assumption_reduction_packet"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_20260525_v0.json"
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
            "reason": "Accepted insufficient-assumptions blocker should route to a bounded assumption-reduction packet.",
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "consumed",
            "reason": "The obstruction-refinement packet result review is consumed by this checkpoint.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "deferred",
            "reason": "A new proof-object attempt requires assumption reduction and review first.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Accepting an assumptions blocker does not close QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this result review.",
        },
    ]


def build_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review(
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
        "selected_blocker_expected": packet.get("selected_primary_blocker")
        == PRIMARY_BLOCKER
        and packet.get("primary_blocker") == PRIMARY_BLOCKER,
        "preserves_proof_object_obstruction_class": packet.get(
            "proof_object_obstruction_class"
        )
        == PROOF_OBJECT_OBSTRUCTION_CLASS,
        "no_proof_object_constructed": packet.get("proof_object_constructed")
        is False
        and packet.get("conservation_proof_object_constructed") is False,
        "no_conservation_witness_constructed": packet.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_or_bianchi_claim": packet.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and packet.get("Bianchi_compatibility_claimed") is False,
        "no_einstein_or_qft_gr_closure": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False
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
        else "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "proof_object_obstruction_class": PROOF_OBJECT_OBSTRUCTION_CLASS,
        "selected_blocker": PRIMARY_BLOCKER,
        "primary_blocker": PRIMARY_BLOCKER,
        "insufficient_assumptions_blocker_accepted": accepted,
        "assumption_reduction_packet_preparation_authorized": accepted,
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
        if accepted
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_RESULT_REVIEW",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_assumption_reduction_packet_preparation"
        ),
        "selected_route": (
            "qft_gr_covariant_conservation_assumption_reduction_packet_preparation_after_insufficient_assumptions_blocker_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_"
            "ONLY_NO_PROOF_OBJECT_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the insufficient-assumptions blocker "
            "from the proof-object obstruction refinement packet and authorizes "
            "assumption-reduction packet preparation. It does not construct a "
            "proof object or conservation witness, claim source admissibility or "
            "Bianchi compatibility, derive the semiclassical Einstein equation, "
            "close QFT-GR, validate empirically, promote the master action, "
            "assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation proof-object obstruction refinement packet result review."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_report: "
        f"accepted={payload['accepted']} blocker={payload['selected_blocker']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
