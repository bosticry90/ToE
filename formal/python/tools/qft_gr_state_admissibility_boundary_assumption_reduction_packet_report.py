from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_state_domain_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_STATE_DOMAIN_PACKET_PATH,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
    STATE_ADMISSIBILITY_BOUNDARY,
)
from formal.python.tools.qft_gr_state_domain_object_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    NEXT_ROW_ID as EXPECTED_SELECTED_ROW_ID,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_ATTEMPT_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_ATTEMPT_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_ATTEMPT_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_ROW_ID as ACCEPTED_PRIOR_ROW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_"
    "20260607_v0"
)
PACKET_ID = "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
    "WITH_NO_SOURCE_ADMISSIBILITY_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_prepared_"
    "with_no_source_admissibility_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
SELECTED_ROW_ID = EXPECTED_SELECTED_ROW_ID
NEXT_TARGET = (
    "review_qft_gr_state_admissibility_boundary_assumption_reduction_packet_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review"
)
STATE_ADMISSIBILITY_BOUNDARY_CONDITION = STATE_ADMISSIBILITY_BOUNDARY
REQUIRED_FUTURE_PROOF_OBJECT = (
    "state_admissibility_boundary_for_meaningful_expectation_functional"
)
CANDIDATE_REDUCTION_ROUTE = (
    "separate state admissibility for expectation-meaningfulness from "
    "stress-energy source admissibility and Bianchi compatibility"
)
FAILURE_MODE_IF_UNRESOLVED = (
    "state-domain admissibility remains conflated with downstream "
    "source-admissibility and conservation obligations"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_"
        "20260607_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _row_by_id(rows: list[dict[str, Any]], assumption_id: str) -> dict[str, Any] | None:
    for row in rows:
        if row.get("assumption_id") == assumption_id:
            return row
    return None


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared SD-ASSUMP-002 packet must be result-reviewed "
                "before any state-admissibility boundary reduction attempt is "
                "authorized."
            ),
        },
        {
            "target": (
                "execute_qft_gr_state_admissibility_boundary_assumption_"
                "reduction_attempt"
            ),
            "decision": "deferred",
            "reason": (
                "A bounded SD-ASSUMP-002 attempt requires packet result review "
                "first."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_state_expectation_compatibility_assumption_"
                "reduction_packet"
            ),
            "decision": "deferred",
            "reason": (
                "SD-ASSUMP-003 remains downstream of SD-ASSUMP-002 packet "
                "review."
            ),
        },
        {
            "target": "claim_qft_gr_state_admissibility",
            "decision": "not_authorized",
            "reason": (
                "Packet preparation records the boundary condition only; it "
                "does not claim state admissibility."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "State admissibility is not stress-energy source admissibility.",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "Packet preparation does not construct a conservation proof object.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "Packet preparation does not construct a conservation witness.",
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
            "reason": "QFT-GR seam closure remains outside this packet.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission remain unauthorized.",
        },
    ]


def _nonclaims() -> dict[str, bool]:
    return {
        "state_admissibility_claimed": False,
        "state_admissibility_discharged": False,
        "state_admissibility_claimed_as_source_admissibility": False,
        "state_admissibility_boundary_satisfied": False,
        "state_admissibility_boundary_discharged": False,
        "state_domain_assumptions_discharged": False,
        "state_domain_assumptions_reduced_or_discharged_by_preparation": False,
        "state_domain_assumptions_reduced_or_discharged_by_implication": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "conservation_proved": False,
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
    }


def build_qft_gr_state_admissibility_boundary_assumption_reduction_packet(
    *,
    attempt_result_review_path: Path = DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    state_domain_packet_path: Path = DEFAULT_STATE_DOMAIN_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt_result_review = _read_json(attempt_result_review_path)
    state_domain_packet = _read_json(state_domain_packet_path)
    rows = state_domain_packet.get("candidate_reducible_assumptions", [])
    selected_row = _row_by_id(rows, SELECTED_ROW_ID)
    selected_status = selected_row.get("current_status", []) if selected_row else []
    candidate_next_targets = _candidate_next_targets()

    selected_row_payload: dict[str, Any] = {}
    if selected_row:
        selected_row_payload = {
            "assumption_id": selected_row["assumption_id"],
            "assumption_family": selected_row["assumption_family"],
            "current_status": selected_row["current_status"],
            "state_admissibility_boundary_condition": (
                STATE_ADMISSIBILITY_BOUNDARY_CONDITION
            ),
            "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY_CONDITION,
            "available_repo_evidence": selected_row["available_repo_evidence"],
            "required_future_proof_object": selected_row[
                "required_future_proof_object"
            ],
            "candidate_reduction_route": selected_row["candidate_reduction_route"],
            "claim_ceiling": (
                "state_admissibility_boundary_packet_only_no_state_"
                "admissibility_claim_no_source_admissibility_no_conservation_"
                "witness"
            ),
            "failure_mode_if_unresolved": selected_row["failure_mode_if_unresolved"],
        }

    acceptance_criteria = {
        "consumes_expected_attempt_result_review": attempt_result_review.get(
            "review_id"
        )
        == EXPECTED_ATTEMPT_RESULT_REVIEW_ID,
        "attempt_result_review_schema_expected": attempt_result_review.get(
            "schema_id"
        )
        == EXPECTED_ATTEMPT_RESULT_REVIEW_SCHEMA_ID,
        "attempt_result_review_outcome_expected": attempt_result_review.get(
            "outcome_id"
        )
        == EXPECTED_ATTEMPT_RESULT_REVIEW_OUTCOME,
        "attempt_result_review_classification_expected": attempt_result_review.get(
            "result_review_classification"
        )
        == EXPECTED_ATTEMPT_RESULT_REVIEW_CLASSIFICATION,
        "attempt_result_review_authorized_this_packet": attempt_result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "accepted_prior_row001": attempt_result_review.get(
            "accepted_state_domain_assumption_row"
        )
        == ACCEPTED_PRIOR_ROW_ID
        and attempt_result_review.get("state_domain_object_assumption_accepted")
        is True,
        "selects_only_row002": selected_row is not None
        and attempt_result_review.get("next_state_domain_assumption_row")
        == SELECTED_ROW_ID,
        "selected_row_status_tokens_current": selected_status
        == ["required", "missing", "candidate_reducible"],
        "preserves_insufficient_assumptions_blocker": attempt_result_review.get(
            "selected_blocker"
        )
        == BLOCKER
        and attempt_result_review.get("conservation_blocker_remains") is True,
        "preserves_state_domain_family": attempt_result_review.get(
            "selected_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY,
        "prior_families_remain_completed": attempt_result_review.get(
            "completed_prior_assumption_families"
        )
        == PRIOR_COMPLETED_FAMILIES,
        "state_domain_inventory_available": bool(rows),
        "state_admissibility_boundary_condition_recorded": selected_row_payload.get(
            "state_admissibility_boundary_condition"
        )
        == STATE_ADMISSIBILITY_BOUNDARY_CONDITION,
        "available_repo_evidence_recorded": bool(
            selected_row_payload.get("available_repo_evidence")
        ),
        "required_future_proof_object_recorded": selected_row_payload.get(
            "required_future_proof_object"
        )
        == REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route_recorded": selected_row_payload.get(
            "candidate_reduction_route"
        )
        == CANDIDATE_REDUCTION_ROUTE,
        "prepares_reduction_analysis_only": bool(selected_row_payload),
        "does_not_claim_state_admissibility": True,
        "does_not_claim_source_admissibility": attempt_result_review.get(
            "source_admissibility_claimed"
        )
        is False
        and attempt_result_review.get("stress_energy_source_admissibility_claimed")
        is False,
        "does_not_construct_conservation_proof_object": attempt_result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and attempt_result_review.get("proof_object_constructed") is False,
        "does_not_construct_conservation_witness": attempt_result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_bianchi_compatibility": attempt_result_review.get(
            "Bianchi_compatibility_claimed"
        )
        is False,
        "does_not_derive_semiclassical_einstein_equation": attempt_result_review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "does_not_close_qft_gr_seam": attempt_result_review.get("qft_gr_seam_closed")
        is False,
        "no_release_or_public_submission": attempt_result_review.get(
            "release_assembly_authorized"
        )
        is False
        and attempt_result_review.get("public_submission_authorized") is False,
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
        else "QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_state_domain_object_assumption_reduction_attempt_result_review": (
            EXPECTED_ATTEMPT_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_state_domain_object_assumption_reduction_attempt_result_review_pointer": _ptr(
            attempt_result_review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_outcome_id": attempt_result_review.get("outcome_id"),
        "consumed_result_review_classification": attempt_result_review.get(
            "result_review_classification"
        ),
        "source_state_domain_assumption_reduction_packet": state_domain_packet.get(
            "packet_id"
        ),
        "source_state_domain_assumption_reduction_packet_pointer": _ptr(
            state_domain_packet_path
        ),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "accepted_prior_state_domain_assumption_row": ACCEPTED_PRIOR_ROW_ID,
        "accepted_state_domain_assumption_rows": [ACCEPTED_PRIOR_ROW_ID],
        "accepted_state_domain_assumption_row_count": 1,
        "selected_state_domain_assumption_row": SELECTED_ROW_ID,
        "selected_row_count": 1 if selected_row_payload else 0,
        "state_admissibility_boundary_condition": (
            STATE_ADMISSIBILITY_BOUNDARY_CONDITION
        ),
        "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY_CONDITION,
        "state_admissibility_boundary_assumption": selected_row_payload,
        "state_admissibility_boundary_status_tokens": selected_status,
        "available_repo_evidence": selected_row_payload.get(
            "available_repo_evidence", []
        ),
        "required_future_proof_object": selected_row_payload.get(
            "required_future_proof_object", REQUIRED_FUTURE_PROOF_OBJECT
        ),
        "candidate_reduction_route": selected_row_payload.get(
            "candidate_reduction_route", CANDIDATE_REDUCTION_ROUTE
        ),
        "claim_ceiling": (
            "state_admissibility_boundary_assumption_reduction_packet_"
            "preparation_only_no_state_admissibility_claim_no_source_"
            "admissibility_no_conservation_witness_no_qft_gr_seam_closure"
        ),
        "failure_mode_if_unresolved": selected_row_payload.get(
            "failure_mode_if_unresolved", FAILURE_MODE_IF_UNRESOLVED
        ),
        "state_admissibility_boundary_assumption_reduction_analysis_prepared": (
            prepared
        ),
        "prepares_reduction_analysis_only": prepared,
        **_nonclaims(),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_"
            "REDUCTION_PACKET"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_route": (
            "qft_gr_state_admissibility_boundary_assumption_reduction_packet_"
            "result_review_after_preparation"
        ),
        "selected_next_authorization_token": OUTCOME_ID if prepared else "",
        "selection_count": 1 if prepared else 0,
        "selected_next_target_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_STATE_ADMISSIBILITY_BOUNDARY_ASSUMPTION_REDUCTION_"
            "PACKET_RESULT_ONLY_NO_STATE_ADMISSIBILITY_CLAIM_SOURCE_"
            "ADMISSIBILITY_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only SD-ASSUMP-002 state-admissibility "
            "boundary reduction analysis. It records the boundary condition, "
            "available repo evidence, required future proof object, candidate "
            "reduction route, claim ceiling, and failure mode. It does not "
            "claim state admissibility, claim source admissibility, construct "
            "a conservation proof object or conservation witness, claim "
            "Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, assemble release, or authorize public "
            "submission."
        ),
    }


def write_qft_gr_state_admissibility_boundary_assumption_reduction_packet(
    *,
    attempt_result_review_path: Path = DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    state_domain_packet_path: Path = DEFAULT_STATE_DOMAIN_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_state_admissibility_boundary_assumption_reduction_packet(
        attempt_result_review_path=attempt_result_review_path,
        state_domain_packet_path=state_domain_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR SD-ASSUMP-002 state-admissibility boundary "
            "assumption-reduction packet."
        )
    )
    parser.add_argument(
        "--attempt-result-review",
        type=Path,
        default=DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    )
    parser.add_argument(
        "--state-domain-packet",
        type=Path,
        default=DEFAULT_STATE_DOMAIN_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_result_review_path = (
        ns.attempt_result_review
        if ns.attempt_result_review.is_absolute()
        else (REPO_ROOT / ns.attempt_result_review)
    )
    state_domain_packet_path = (
        ns.state_domain_packet
        if ns.state_domain_packet.is_absolute()
        else (REPO_ROOT / ns.state_domain_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_state_admissibility_boundary_assumption_reduction_packet(
        attempt_result_review_path=attempt_result_review_path,
        state_domain_packet_path=state_domain_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_state_admissibility_boundary_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} row={payload['selected_state_domain_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
