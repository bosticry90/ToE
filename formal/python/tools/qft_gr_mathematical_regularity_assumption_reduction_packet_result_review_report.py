from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIOR_COMPLETED_FAMILIES,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW,
    NEXT_TARGET as CONSUMED_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_20260608_v0"
)
REVIEW_ID = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_MR_ASSUMP_001_"
    "ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review_"
    "accepts_packet_and_authorizes_bounded_mr_assump_001_attempt_only"
)
NEXT_TARGET = (
    "execute_qft_gr_derivative_exchange_regular_boundary_"
    "assumption_reduction_attempt"
)
NEXT_TARGET_KIND = (
    "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_"
    "attempt_execution"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_20260608_v0.json"
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
            "reason": (
                "The packet has been accepted as preparation only, so the next "
                "bounded action is the MR-ASSUMP-001 derivative-exchange "
                "regular-boundary reduction attempt. This review does not "
                "execute that attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "The mathematical-regularity packet review target is consumed "
                "by this result-review checkpoint."
            ),
        },
        {
            "target": "execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt",
            "decision": "not_authorized_current_row",
            "reason": (
                "MR-ASSUMP-002 remains downstream; only MR-ASSUMP-001 is "
                "authorized after this packet review."
            ),
        },
        {
            "target": "execute_qft_gr_distributional_pairing_regular_domain_assumption_reduction_attempt",
            "decision": "not_authorized_current_row",
            "reason": (
                "MR-ASSUMP-003 remains downstream; only MR-ASSUMP-001 is "
                "authorized after this packet review."
            ),
        },
        {
            "target": "execute_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt",
            "decision": "not_authorized_current_row",
            "reason": (
                "MR-ASSUMP-004 remains downstream; only MR-ASSUMP-001 is "
                "authorized after this packet review."
            ),
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": "Source admissibility remains downstream and unclaimed.",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": (
                "Packet result review does not construct or authorize a "
                "conservation proof object."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized.",
        },
        {
            "target": "claim_qft_gr_state_admissibility",
            "decision": "not_authorized",
            "reason": "Mathematical-regularity packet review does not imply state admissibility.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "Mathematical-regularity packet review does not imply source admissibility.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains explicitly outside scope.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission are outside this checkpoint.",
        },
    ]


def build_qft_gr_mathematical_regularity_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    selected_row = packet.get("selected_mathematical_regularity_assumption", {})

    acceptance_criteria = {
        "consumes_expected_mathematical_regularity_packet": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_and_result_review_selected_targets_split": NEXT_TARGET
        != CONSUMED_TARGET,
        "packet_prepared_and_accepted_only": packet.get("prepared") is True
        and packet.get("accepted") is True
        and packet.get("prepares_reduction_analysis_only") is True,
        "selected_family_is_mathematical_regularity": packet.get(
            "selected_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY,
        "selected_row_is_mr_assump_001": packet.get(
            "selected_bounded_mathematical_regularity_assumption_row"
        )
        == SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        and selected_row.get("assumption_id")
        == SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        and selected_row.get("assumption_family") == SELECTED_ASSUMPTION_FAMILY,
        "selected_row_records_derivative_exchange_boundary": packet.get(
            "derivative_exchange_regular_boundary"
        )
        == DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY
        and selected_row.get("regularity_condition")
        == DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
        "prior_completed_families_preserved": packet.get(
            "completed_prior_assumption_families"
        )
        == PRIOR_COMPLETED_FAMILIES
        and packet.get("completed_prior_assumption_family_count") == 3
        and packet.get("operator_domain_assumptions_completed") is True
        and packet.get("renormalization_assumptions_completed") is True
        and packet.get("state_domain_assumptions_completed") is True,
        "broader_conservation_blocker_preserved": packet.get("blocker") == BLOCKER
        and packet.get("conservation_blocker_remains") is True,
        "review_does_not_execute_attempt": True,
        "packet_does_not_discharge_mathematical_regularity": packet.get(
            "mathematical_regularity_assumptions_discharged"
        )
        is False
        and packet.get(
            "mathematical_regularity_assumptions_reduced_or_discharged_by_preparation"
        )
        is False,
        "no_state_admissibility": packet.get("state_admissibility_claimed")
        is False,
        "no_source_admissibility": packet.get("source_admissibility_claimed")
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_proof": packet.get("conservation_proved") is False
        and packet.get("actual_conservation_claimed") is False,
        "no_conservation_proof_object": packet.get(
            "conservation_proof_object_constructed"
        )
        is False
        and packet.get("proof_object_constructed") is False,
        "no_conservation_witness": packet.get("conservation_witness_constructed")
        is False,
        "no_bianchi_compatibility": packet.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_derivation": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": packet.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": packet.get("empirical_validation_claimed")
        is False,
        "no_master_action_promotion": packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": packet.get("release_assembly_authorized")
        is False
        and packet.get("release_packet_assembled") is False
        and packet.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    accepted = all(acceptance_criteria.values())
    selected_result_review_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW"
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_REJECTS_OR_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review_rejects_or_requires_remediation",
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_mathematical_regularity_assumption_reduction_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_mathematical_regularity_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "packet_selected_next_target": CONSUMED_TARGET,
        "result_review_selected_next_target": selected_result_review_next_target,
        "mathematical_regularity_assumption_reduction_packet_selected_next_target": (
            CONSUMED_TARGET
        ),
        "mathematical_regularity_assumption_reduction_packet_result_review_selected_next_target": (
            selected_result_review_next_target
        ),
        "packet_result_review_selected_target_split_preserved": (
            accepted and selected_result_review_next_target != CONSUMED_TARGET
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "broader_blocker_resolution_required": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "operator_domain_assumptions_completed": True,
        "renormalization_assumptions_completed": True,
        "state_domain_assumptions_completed": True,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_mathematical_regularity_assumption_row": (
            SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        ),
        "selected_bounded_mathematical_regularity_assumption_row": (
            SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        ),
        "selected_row_count": 1,
        "selected_row_is_first_repo_authoritative_row": True,
        "derivative_exchange_regular_boundary": DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
        "mathematical_regularity_assumption_reduction_packet_reviewed": accepted,
        "mathematical_regularity_assumption_reduction_packet_accepted": accepted,
        "mathematical_regularity_assumption_reduction_packet_rejected": not accepted,
        "mathematical_regularity_assumption_reduction_packet_preparation_only": True,
        "packet_preparation_only_confirmed_by_review": accepted,
        "mr_assump_001_attempt_executed_by_review": False,
        "derivative_exchange_regular_boundary_assumption_reduction_attempt_authorized": (
            accepted
        ),
        "derivative_exchange_regular_boundary_assumption_reduction_attempt_executed": (
            False
        ),
        "mathematical_regularity_assumptions_discharged": False,
        "mathematical_regularity_assumptions_reduced_or_discharged_by_review": False,
        "assumptions_reduced_or_discharged_by_review": False,
        "state_admissibility_claimed": False,
        "state_admissibility_discharged": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "conservation_proved": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
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
        "selected_next_target": selected_result_review_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_route": (
            "qft_gr_derivative_exchange_regular_boundary_assumption_reduction_"
            "attempt_after_mathematical_regularity_packet_result_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY_ASSUMPTION_"
            "REDUCTION_ATTEMPT_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the mathematical-regularity "
            "assumption-reduction packet and authorizes the bounded "
            "MR-ASSUMP-001 derivative-exchange regular-boundary attempt. It "
            "does not execute that attempt, reduce or discharge mathematical "
            "regularity assumptions, claim state admissibility, claim source "
            "admissibility, prove conservation, construct a conservation proof "
            "object or witness, claim Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_mathematical_regularity_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_mathematical_regularity_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR mathematical-regularity assumption-reduction "
            "packet result review."
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
    payload = write_qft_gr_mathematical_regularity_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} "
        f"row={payload['selected_mathematical_regularity_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
