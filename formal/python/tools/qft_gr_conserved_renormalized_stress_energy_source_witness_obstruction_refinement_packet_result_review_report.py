from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_attempt_result_review_report import (
    MISSING_CONDITION_CANDIDATES,
)
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIMARY_MISSING_CONDITION,
    PRIMARY_OBSTRUCTION_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-05-25T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_20260525_v0"
)
REVIEW_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_RESULT_REVIEW_ACCEPTS_CONSERVATION_AS_PRIMARY_"
    "OBSTRUCTION_AND_AUTHORIZES_CONSERVATION_WITNESS_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_conserved_renormalized_source_witness_obstruction_refinement_"
    "result_review_accepts_conservation_primary_and_authorizes_conservation_"
    "witness_packet_preparation_only"
)
CONSUMED_TARGET = (
    "review_qft_gr_conserved_renormalized_stress_energy_source_witness_"
    "obstruction_refinement_packet_result"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
    "OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_20260525_v0.json"
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
            "reason": "The reviewed primary obstruction is conservation, so only the conservation witness packet is authorized.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_finiteness_witness_packet",
            "decision": "deferred",
            "reason": "Finiteness remains on the menu but is not the accepted primary obstruction.",
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_witness_packet",
            "decision": "deferred",
            "reason": "Bianchi compatibility remains downstream of conservation.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Packet result review does not close the QFT-GR seam.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this result review.",
        },
    ]


def build_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review(
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
        "packet_selected_conservation_witness_packet": packet.get("selected_next_target")
        == NEXT_TARGET,
        "full_missing_condition_menu_preserved": packet.get("missing_condition_menu")
        == MISSING_CONDITION_CANDIDATES,
        "primary_obstruction_is_conservation": packet.get("primary_obstruction_id")
        == PRIMARY_OBSTRUCTION_ID
        and packet.get("primary_missing_condition") == PRIMARY_MISSING_CONDITION,
        "no_obstruction_solved_or_witness_constructed": packet.get(
            "primary_obstruction_solved"
        )
        is False
        and packet.get("witness_constructed") is False
        and packet.get("completed_witness_constructed") is False,
        "no_qft_gr_closure_or_einstein_derivation": packet.get("qft_gr_seam_closed")
        is False
        and packet.get("semiclassical_einstein_equation_derived") is False,
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
        else "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "obstruction_refinement_packet_result_reviewed": accepted,
        "conservation_primary_obstruction_accepted": accepted,
        "missing_condition_menu": MISSING_CONDITION_CANDIDATES,
        "primary_obstruction_id": PRIMARY_OBSTRUCTION_ID,
        "primary_missing_condition": PRIMARY_MISSING_CONDITION,
        "primary_obstruction_solved": False,
        "conservation_witness_packet_preparation_authorized": accepted,
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
        if accepted
        else "REMEDIATE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "qft_gr_stress_energy_conservation_witness_packet_preparation",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_STRESS_ENERGY_CONSERVATION_WITNESS_PACKET_ONLY_"
            "NO_WITNESS_CONSTRUCTION_OR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts conservation as the primary QFT-GR source "
            "witness obstruction and authorizes only conservation witness packet "
            "preparation. It does not solve the obstruction, construct a witness, "
            "derive the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or authorize "
            "public submission."
        ),
    }


def write_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR source witness obstruction refinement packet result review."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
