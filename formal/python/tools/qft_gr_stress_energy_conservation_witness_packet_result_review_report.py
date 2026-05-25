from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_stress_energy_conservation_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    POST_PACKET_REVIEW_TARGET,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW_20260525_v0"
REVIEW_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_CONSERVATION_WITNESS_ATTEMPT_ONLY"
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_stress_energy_conservation_witness_packet_result_review_accepts_"
    "packet_and_authorizes_bounded_conservation_witness_attempt_only"
)
CONSUMED_TARGET = "review_qft_gr_stress_energy_conservation_witness_packet_result"
NEXT_TARGET = "execute_qft_gr_stress_energy_conservation_witness_attempt"
EXECUTION_CLASSIFICATIONS = [
    "qft_gr_stress_energy_conservation_witness_constructed_pending_result_review",
    "qft_gr_stress_energy_conservation_obstruction_identified_requires_refinement",
    "qft_gr_stress_energy_conservation_inconclusive_requires_assumption_reduction",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def build_qft_gr_stress_energy_conservation_witness_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The conservation witness packet is accepted, so only the bounded conservation witness attempt is authorized.",
        },
        {
            "target": "review_qft_gr_stress_energy_conservation_witness_attempt_result",
            "decision": "deferred",
            "reason": "Attempt result review requires an execution result first.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Packet result review does not close QFT-GR.",
        },
    ]
    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "primary_obstruction_preserved": packet.get("primary_missing_condition")
        == "conservation"
        and packet.get("primary_obstruction_preserved") is True,
        "packet_preparation_only": packet.get("prepared") is True
        and packet.get("conservation_witness_constructed") is False,
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
        "post_packet_target_expected": packet.get("post_packet_review_target")
        == POST_PACKET_REVIEW_TARGET,
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
        else "QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_stress_energy_conservation_witness_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_stress_energy_conservation_witness_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "primary_missing_condition": "conservation",
        "primary_obstruction_preserved": True,
        "packet_preparation_only_confirmed": accepted,
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
        "bounded_conservation_witness_attempt_authorized": accepted,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "qft_gr_stress_energy_conservation_witness_attempt_execution",
        "selection_count": 1 if accepted else 0,
        "future_execution_classifications": EXECUTION_CLASSIFICATIONS,
        "next_action_scope": (
            "EXECUTE_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_ATTEMPT_ONLY_"
            "NO_QFT_GR_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the conservation witness packet and "
            "authorizes only a bounded conservation witness attempt. It does not "
            "construct the witness, claim stress-energy source admissibility or "
            "Bianchi compatibility, derive the semiclassical Einstein equation, "
            "close QFT-GR, validate empirically, promote the master action, "
            "assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_stress_energy_conservation_witness_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_stress_energy_conservation_witness_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR stress-energy conservation witness packet result review."
    )
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_stress_energy_conservation_witness_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_stress_energy_conservation_witness_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
