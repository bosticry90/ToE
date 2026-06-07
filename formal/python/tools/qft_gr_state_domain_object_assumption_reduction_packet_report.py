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
    PACKET_ID as EXPECTED_STATE_DOMAIN_PACKET_ID,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
    STATE_ADMISSIBILITY_BOUNDARY,
    STATE_DOMAIN_OBJECT,
)
from formal.python.tools.qft_gr_state_domain_assumption_reduction_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_BOUNDED_STATE_DOMAIN_ROW,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_20260607_v0"
PACKET_ID = "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduction_packet_prepared_with_no_"
    "conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
SELECTED_ROW_ID = SELECTED_BOUNDED_STATE_DOMAIN_ROW
NEXT_TARGET = "review_qft_gr_state_domain_object_assumption_reduction_packet_result"
STATE_OBJECT_COMPATIBILITY_CONDITION = (
    "bounded_qft_state_domain_object_compatible_with_candidate_renormalized_"
    "stress_energy_expectation_without_source_admissibility_claim"
)
STATE_DOMAIN_OBJECT_DEFINITION_STATUS = (
    "candidate_state_domain_object_selected_for_reduction_analysis_not_final_"
    "state_admissibility_or_conservation_discharge"
)
REQUIRED_FUTURE_PROOF_OBJECT = (
    "bounded_qft_state_domain_object_for_candidate_renormalized_source"
)
CANDIDATE_REDUCTION_ROUTE = (
    "pin the bounded QFT state-domain object where the candidate "
    "renormalized stress-energy expectation is meaningful, while separating "
    "that object from state admissibility, source admissibility, Bianchi "
    "compatibility, and conservation"
)
FAILURE_MODE_IF_UNRESOLVED = (
    "the candidate renormalized expectation remains meaningful only over an "
    "unspecified state class, blocking any later conservation proof object"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_20260607_v0.json"
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
                "The prepared SD-ASSUMP-001 packet must be result-reviewed "
                "before any state-domain object reduction attempt is authorized."
            ),
        },
        {
            "target": "execute_qft_gr_state_domain_object_assumption_reduction_attempt",
            "decision": "deferred",
            "reason": "A bounded SD-ASSUMP-001 attempt requires packet result review first.",
        },
        {
            "target": "prepare_qft_gr_state_admissibility_boundary_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "SD-ASSUMP-002 remains downstream of SD-ASSUMP-001 packet review.",
        },
        {
            "target": "prepare_qft_gr_state_expectation_compatibility_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "SD-ASSUMP-003 remains downstream of SD-ASSUMP-001 packet review.",
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
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "A state-domain object is not a source-admissibility proof.",
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


def build_qft_gr_state_domain_object_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    state_domain_packet_path: Path = DEFAULT_STATE_DOMAIN_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
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
            "state_domain_object": STATE_DOMAIN_OBJECT,
            "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY,
            "state_object_compatibility_condition": (
                STATE_OBJECT_COMPATIBILITY_CONDITION
            ),
            "state_domain_object_definition_status": (
                STATE_DOMAIN_OBJECT_DEFINITION_STATUS
            ),
            "available_repo_evidence": selected_row["available_repo_evidence"],
            "required_future_proof_object": selected_row[
                "required_future_proof_object"
            ],
            "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
            "claim_ceiling": (
                "state_domain_object_packet_only_no_state_admissibility_"
                "discharge_no_source_admissibility_no_conservation_witness"
            ),
            "failure_mode_if_unresolved": FAILURE_MODE_IF_UNRESOLVED,
        }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
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
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == BLOCKER
        and result_review.get("conservation_blocker_remains") is True,
        "preserves_state_domain_family": result_review.get(
            "selected_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY,
        "source_state_domain_packet_available": state_domain_packet.get("packet_id")
        == EXPECTED_STATE_DOMAIN_PACKET_ID,
        "prior_families_remain_completed": result_review.get(
            "completed_prior_assumption_families"
        )
        == PRIOR_COMPLETED_FAMILIES,
        "selects_only_state_domain_object_row": selected_row is not None
        and result_review.get("selected_bounded_state_domain_assumption_row")
        == SELECTED_ROW_ID,
        "selected_row_status_tokens_current": selected_status
        == ["required", "supplied", "candidate_reducible"],
        "state_domain_object_recorded": selected_row_payload.get(
            "state_domain_object"
        )
        == STATE_DOMAIN_OBJECT,
        "state_admissibility_boundary_recorded_without_claim": selected_row_payload.get(
            "state_admissibility_boundary"
        )
        == STATE_ADMISSIBILITY_BOUNDARY,
        "state_object_compatibility_condition_recorded": selected_row_payload.get(
            "state_object_compatibility_condition"
        )
        == STATE_OBJECT_COMPATIBILITY_CONDITION,
        "prepares_reduction_analysis_only": bool(selected_row_payload),
        "does_not_discharge_state_domain_object_assumption": True,
        "does_not_claim_state_admissibility_discharge": True,
        "does_not_construct_conservation_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed") is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_source_admissibility": result_review.get(
            "source_admissibility_claimed"
        )
        is False
        and result_review.get("stress_energy_source_admissibility_claimed") is False,
        "does_not_claim_bianchi_compatibility": result_review.get(
            "Bianchi_compatibility_claimed"
        )
        is False,
        "does_not_derive_semiclassical_einstein_equation": result_review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "does_not_close_qft_gr_seam": result_review.get("qft_gr_seam_closed")
        is False,
        "does_not_claim_empirical_validation": result_review.get(
            "empirical_validation_claimed"
        )
        is False,
        "does_not_promote_master_action": result_review.get(
            "master_action_promoted"
        )
        is False
        and result_review.get("master_action_promotion_authorized") is False,
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
        else "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_state_domain_assumption_reduction_packet_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_state_domain_assumption_reduction_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "source_state_domain_assumption_reduction_packet": (
            EXPECTED_STATE_DOMAIN_PACKET_ID
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
        "selected_state_domain_assumption_row": SELECTED_ROW_ID,
        "selected_row_count": 1 if selected_row_payload else 0,
        "state_domain_object": STATE_DOMAIN_OBJECT,
        "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY,
        "state_object_compatibility_condition": STATE_OBJECT_COMPATIBILITY_CONDITION,
        "state_domain_object_definition_status": (
            STATE_DOMAIN_OBJECT_DEFINITION_STATUS
        ),
        "state_domain_object_assumption": selected_row_payload,
        "state_domain_object_status_tokens": selected_status,
        "available_repo_evidence": selected_row_payload.get(
            "available_repo_evidence", []
        ),
        "required_future_proof_object": selected_row_payload.get(
            "required_future_proof_object", REQUIRED_FUTURE_PROOF_OBJECT
        ),
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "claim_ceiling": (
            "state_domain_object_assumption_reduction_packet_preparation_only_"
            "no_state_admissibility_discharge_no_conservation_witness_no_"
            "qft_gr_seam_closure"
        ),
        "failure_mode_if_unresolved": FAILURE_MODE_IF_UNRESOLVED,
        "state_domain_object_assumption_reduction_analysis_prepared": prepared,
        "prepares_reduction_analysis_only": prepared,
        "state_domain_object_assumption_discharged": False,
        "state_domain_object_assumption_reduced_or_discharged_by_preparation": False,
        "state_domain_assumptions_discharged": False,
        "state_domain_assumptions_reduced_or_discharged_by_preparation": False,
        "state_admissibility_discharged": False,
        "state_admissibility_claimed_as_source_admissibility": False,
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
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_state_domain_object_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_state_domain_object_assumption_reduction_packet_result_review_"
            "after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_"
            "ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only SD-ASSUMP-001 state-domain object "
            "reduction analysis. It does not discharge state-domain "
            "assumptions, construct a conservation proof object or "
            "conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_state_domain_object_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    state_domain_packet_path: Path = DEFAULT_STATE_DOMAIN_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_state_domain_object_assumption_reduction_packet(
        result_review_path=result_review_path,
        state_domain_packet_path=state_domain_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR SD-ASSUMP-001 state-domain object packet."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
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
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    state_domain_packet_path = (
        ns.state_domain_packet
        if ns.state_domain_packet.is_absolute()
        else (REPO_ROOT / ns.state_domain_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_state_domain_object_assumption_reduction_packet(
        result_review_path=result_review_path,
        state_domain_packet_path=state_domain_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_state_domain_object_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} row={payload['selected_state_domain_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
