from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIOR_COMPLETED_FAMILY,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SELECTED_ASSUMPTION_FAMILY,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "20260606_v0"
)
REVIEW_ID = "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "RENORMALIZATION_FAMILY_ANALYSIS_AND_AUTHORIZES_NEXT_BOUNDED_"
    "RENORMALIZATION_TARGET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalization_assumption_reduction_packet_result_review_accepts_"
    "renormalization_family_analysis_and_authorizes_next_bounded_"
    "renormalization_target_only"
)
SELECTED_BOUNDED_RENORMALIZATION_ROW = (
    "RN-ASSUMP-001-renormalized_stress_energy_object"
)
NEXT_TARGET = (
    "prepare_qft_gr_renormalized_stress_energy_object_assumption_reduction_"
    "packet"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
        "20260606_v0.json"
    )
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
            "assumption_id": SELECTED_BOUNDED_RENORMALIZATION_ROW,
            "reason": (
                "The candidate renormalized stress-energy object must be fixed "
                "before renormalization scope, finiteness, or compatibility "
                "rows can be reduced."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_renormalization_scope_assumption_reduction_packet"
            ),
            "decision": "deferred",
            "assumption_id": "RN-ASSUMP-002-renormalization_scope",
            "reason": "Renormalization scope remains downstream of object selection.",
        },
        {
            "target": (
                "prepare_qft_gr_renormalized_expectation_finiteness_"
                "assumption_reduction_packet"
            ),
            "decision": "deferred",
            "assumption_id": "RN-ASSUMP-004-finiteness_regular_boundary",
            "reason": (
                "Finiteness and regularity boundaries remain downstream of the "
                "selected renormalized stress-energy object."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-002-conservation-proof-object",
            "reason": "Packet result review does not construct a proof object.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-003-conservation-witness",
            "reason": "No conservation witness is constructed or authorized.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-004-source-admissibility",
            "reason": "Source admissibility remains downstream and unclaimed.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-005-bianchi-compatibility",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-006-semiclassical-einstein-equation",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-007-qft-gr-seam-closure",
            "reason": "QFT-GR seam closure remains outside this review.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "assumption_id": "RN-NONRED-008-release-or-public-submission",
            "reason": "Release assembly and public submission remain unauthorized.",
        },
    ]


def _row_by_id(rows: list[dict[str, Any]], assumption_id: str) -> dict[str, Any] | None:
    for row in rows:
        if row.get("assumption_id") == assumption_id:
            return row
    return None


def build_qft_gr_renormalization_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_rows = packet.get("candidate_reducible_assumptions", [])
    selected_row = _row_by_id(candidate_rows, SELECTED_BOUNDED_RENORMALIZATION_ROW)
    selected_row_status = selected_row.get("current_status", []) if selected_row else []
    candidate_next_targets = _candidate_next_targets()
    selected_next_target_count = sum(
        1 for row in candidate_next_targets if row["decision"] == "selected"
    )

    acceptance_criteria = {
        "consumes_expected_renormalization_packet": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": packet.get("blocker")
        == BLOCKER
        and packet.get("selected_blocker") == BLOCKER
        and packet.get("conservation_blocker_remains") is True,
        "prior_operator_domain_closeout_accepted": packet.get(
            "prior_completed_family"
        )
        == PRIOR_COMPLETED_FAMILY
        and packet.get("prior_completed_operator_domain_assumption_row_count") == 6
        and bool(packet.get("consumed_result_review_outcome_id")),
        "selected_family_is_renormalization": packet.get(
            "selected_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY
        and packet.get("primary_assumption_reduction_family")
        == SELECTED_ASSUMPTION_FAMILY,
        "confirms_packet_preparation_only": packet.get("prepared") is True
        and packet.get("renormalization_assumption_reduction_analysis_prepared")
        is True
        and packet.get("prepares_reduction_analysis_only") is True,
        "no_renormalization_assumption_discharged_by_review": packet.get(
            "renormalization_assumptions_discharged"
        )
        is False
        and packet.get(
            "renormalization_assumptions_reduced_or_discharged_by_preparation"
        )
        is False,
        "selected_first_bounded_row_present": selected_row is not None
        and "candidate_reducible" in selected_row_status,
        "candidate_reducible_rows_current_family": packet.get(
            "candidate_reducible_assumption_count"
        )
        == 5
        and all(
            row.get("assumption_family") == SELECTED_ASSUMPTION_FAMILY
            for row in candidate_rows
        ),
        "no_conservation_proof_object_or_witness": packet.get(
            "conservation_proof_object_constructed"
        )
        is False
        and packet.get("proof_object_constructed") is False
        and packet.get("conservation_witness_constructed") is False,
        "no_source_admissibility_or_bianchi": packet.get(
            "source_admissibility_claimed"
        )
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False
        and packet.get("Bianchi_compatibility_claimed") is False,
        "no_semiclassical_einstein_derivation": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": packet.get("qft_gr_seam_closed") is False,
        "no_empirical_validation_or_master_action_promotion": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": packet.get(
            "release_assembly_authorized"
        )
        is False
        and packet.get("release_packet_assembled") is False
        and packet.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": selected_next_target_count == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    accepted = all(bool(value) for value in acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_renormalization_assumption_reduction_packet_result_review_"
            "blocked"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_renormalization_assumption_reduction_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_renormalization_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "prior_completed_family": PRIOR_COMPLETED_FAMILY,
        "prior_operator_domain_closeout_accepted": accepted,
        "prior_operator_domain_closeout_result_review_outcome_id": packet.get(
            "consumed_result_review_outcome_id"
        ),
        "prior_completed_operator_domain_assumption_rows": packet.get(
            "prior_completed_operator_domain_assumption_rows", []
        ),
        "prior_completed_operator_domain_assumption_row_count": packet.get(
            "prior_completed_operator_domain_assumption_row_count"
        ),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "renormalization_family_analysis_accepted": accepted,
        "renormalization_assumption_reduction_packet_reviewed": accepted,
        "renormalization_assumption_reduction_packet_accepted": accepted,
        "renormalization_assumption_reduction_packet_rejected": not accepted,
        "packet_preparation_only_confirmed": accepted,
        "renormalization_assumptions_discharged_by_review": False,
        "renormalization_assumptions_reduced_or_discharged_by_review": False,
        "renormalization_assumption_reduction_attempt_authorized_by_review": False,
        "selected_bounded_renormalization_assumption_row": (
            SELECTED_BOUNDED_RENORMALIZATION_ROW
        ),
        "selected_bounded_renormalization_assumption_row_status": (
            "candidate_reducible|pending_packet"
        ),
        "selected_bounded_renormalization_assumption_target": NEXT_TARGET,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_renormalized_stress_energy_object_assumption_reduction_"
            "packet_preparation"
        ),
        "selected_next_target_count": selected_next_target_count if accepted else 0,
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_"
            "REDUCTION_PACKET_ONLY_NO_ASSUMPTION_DISCHARGE_CONSERVATION_"
            "WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "conservation_proved": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "source_admissibility_claimed": False,
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
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts the renormalization-family analysis "
            "only and authorizes exactly one bounded renormalization packet "
            "target. It does not discharge renormalization assumptions, "
            "construct a conservation proof object or witness, claim source "
            "admissibility or Bianchi compatibility, derive the semiclassical "
            "Einstein equation, close QFT-GR, validate empirically, promote the "
            "master action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_renormalization_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_renormalization_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR renormalization assumption-reduction packet "
            "result review."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_renormalization_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_renormalization_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
