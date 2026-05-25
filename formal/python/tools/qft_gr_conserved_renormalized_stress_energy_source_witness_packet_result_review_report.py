from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    EXECUTION_CLASSIFICATIONS,
    EXECUTION_TARGET,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_"
    "RESULT_REVIEW_20260525_v0"
)
REVIEW_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_"
    "RESULT_REVIEW_ACCEPTS_WITNESS_PACKET_AND_AUTHORIZES_BOUNDED_WITNESS_"
    "ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_conserved_renormalized_source_witness_packet_result_review_accepts_"
    "packet_and_authorizes_bounded_witness_attempt_only_no_closure_or_empirical_"
    "validation"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = EXECUTION_TARGET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_"
    "RESULT_REVIEW_20260525_v0.json"
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
            "reason": "The prepared witness packet is accepted and authorizes only the bounded witness attempt.",
        },
        {
            "target": "construct_qft_gr_conserved_renormalized_source_witness_as_claim",
            "decision": "not_authorized",
            "reason": "The result review authorizes an attempt, not a witness construction claim.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Packet result review does not close the QFT-GR seam.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains outside this Track 2 result review.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this scientific packet review.",
        },
    ]


def build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review(
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
        "track1_clearance_not_scientific_evidence": packet.get(
            "control_lane_clearance_only"
        )
        is True
        and packet.get("criticizability_readiness_treated_as_scientific_evidence")
        is False,
        "packet_preparation_only_confirmed": packet.get("witness_packet_prepared")
        is True
        and packet.get("witness_constructed") is False,
        "no_witness_or_source_claim": packet.get("witness_constructed") is False
        and packet.get("conserved_renormalized_stress_energy_source_exists_claimed")
        is False,
        "no_einstein_derivation_or_qft_gr_closure": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False
        and packet.get("qft_gr_seam_closed") is False
        and packet.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_master_release_or_public_submission": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("master_action_promoted") is False
        and packet.get("release_assembly_authorized") is False
        and packet.get("public_submission_authorized") is False,
        "allowed_execution_classifications_preserved": packet.get(
            "execution_classification_options"
        )
        == EXECUTION_CLASSIFICATIONS,
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
        else "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "track1_clearance_treated_as_scientific_evidence": False,
        "control_lane_clearance_only": True,
        "witness_packet_result_reviewed": accepted,
        "witness_packet_accepted": accepted,
        "witness_packet_preparation_only_confirmed": accepted,
        "bounded_witness_attempt_authorized": accepted,
        "witness_attempt_executed": False,
        "witness_constructed": False,
        "conserved_renormalized_stress_energy_source_exists_claimed": False,
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
        "source_map_seam_pillar_master_action_promotion_authorized": False,
        "execution_classification_options": EXECUTION_CLASSIFICATIONS,
        "execution_classification_selected": None,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "qft_gr_conserved_renormalized_source_witness_attempt_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_"
            "WITNESS_ATTEMPT_ONLY_NO_CLOSURE_OR_EMPIRICAL_VALIDATION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the prepared QFT-GR conserved renormalized "
            "stress-energy source witness packet and authorizes only a bounded "
            "witness attempt. It does not construct the witness, claim a conserved "
            "renormalized source exists, derive the semiclassical Einstein equation, "
            "close the QFT-GR seam, validate empirically, promote the master action, "
            "assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR conserved renormalized stress-energy source witness packet result review."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
