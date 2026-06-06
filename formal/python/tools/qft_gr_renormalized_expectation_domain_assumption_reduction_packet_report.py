from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_RENORMALIZATION_PACKET_PATH,
    PACKET_ID as EXPECTED_RENORMALIZATION_PACKET_ID,
    PRIOR_COMPLETED_FAMILY,
    RENORMALIZATION_SCOPE,
    RENORMALIZED_EXPECTATION_DOMAIN,
    RENORMALIZED_STRESS_ENERGY_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalization_scope_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    NEXT_ROW_ID as EXPECTED_SELECTED_DOMAIN_ROW,
    NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_ATTEMPT_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_ATTEMPT_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_ATTEMPT_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_renormalization_scope_assumption_reduction_packet_report import (
    SELECTED_ROW_ID as ACCEPTED_PRIOR_SCOPE_ROW,
)
from formal.python.tools.qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_report import (
    SELECTED_ROW_ID as ACCEPTED_PRIOR_OBJECT_ROW,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260606_v0"
)
PACKET_ID = "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
SELECTED_ROW_ID = EXPECTED_SELECTED_DOMAIN_ROW
ACCEPTED_PRIOR_ROWS = [ACCEPTED_PRIOR_OBJECT_ROW, ACCEPTED_PRIOR_SCOPE_ROW]
NEXT_TARGET = (
    "review_qft_gr_renormalized_expectation_domain_assumption_reduction_packet_result"
)
RENORMALIZED_EXPECTATION_DOMAIN_STATUS = (
    "renormalized_expectation_domain_selected_for_reduction_analysis_not_"
    "renormalization_assumption_discharge"
)
DOMAIN_BOUNDARY = [
    "repo_local_renormalized_expectation_domain_only",
    "selected_operator_domain_structure_only",
    "no_finiteness_regular_boundary_claim",
    "no_source_admissibility_claim",
    "no_conservation_claim",
    "no_bianchi_compatibility_claim",
    "no_qft_gr_seam_closure",
]
REQUIRED_FUTURE_PROOF_OBJECT = NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT
CANDIDATE_REDUCTION_ROUTE = (
    "reuse the accepted operator-domain structure to pin the renormalized "
    "expectation domain without asserting conservation"
)
FAILURE_MODE_IF_UNRESOLVED = (
    "the renormalized source may remain meaningful only outside the selected "
    "conservation operator domain"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260606_v0.json"
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
                "The prepared RN-ASSUMP-003 renormalized-expectation-domain "
                "packet must be result-reviewed before any reduction attempt "
                "or downstream finiteness row is authorized."
            ),
        },
        {
            "target": (
                "execute_qft_gr_renormalized_expectation_domain_assumption_"
                "reduction_attempt"
            ),
            "decision": "deferred",
            "reason": "A bounded reduction attempt requires packet result review first.",
        },
        {
            "target": (
                "prepare_qft_gr_renormalized_expectation_finiteness_assumption_"
                "reduction_packet"
            ),
            "decision": "deferred",
            "reason": (
                "Finiteness and regularity are tracked downstream as "
                "RN-ASSUMP-004-finiteness_regular_boundary."
            ),
        },
        {
            "target": "discharge_qft_gr_renormalized_expectation_domain_assumption",
            "decision": "not_authorized",
            "reason": "Packet preparation does not discharge the domain assumption.",
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
            "reason": "The domain packet does not claim source admissibility.",
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


def build_qft_gr_renormalized_expectation_domain_assumption_reduction_packet(
    *,
    attempt_result_review_path: Path = DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    renormalization_packet_path: Path = DEFAULT_RENORMALIZATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(attempt_result_review_path)
    renormalization_packet = _read_json(renormalization_packet_path)
    rows = renormalization_packet.get("candidate_reducible_assumptions", [])
    selected_row = _row_by_id(rows, SELECTED_ROW_ID)
    selected_status = selected_row.get("current_status", []) if selected_row else []
    candidate_next_targets = _candidate_next_targets()

    selected_row_payload: dict[str, Any] = {}
    if selected_row:
        selected_row_payload = {
            "assumption_id": selected_row["assumption_id"],
            "assumption_family": selected_row["assumption_family"],
            "current_status": selected_row["current_status"],
            "renormalized_expectation_domain_object": RENORMALIZED_EXPECTATION_DOMAIN,
            "renormalized_expectation_domain_status": (
                RENORMALIZED_EXPECTATION_DOMAIN_STATUS
            ),
            "domain_boundary": DOMAIN_BOUNDARY,
            "available_repo_evidence": selected_row["available_repo_evidence"],
            "required_future_proof_object": selected_row[
                "required_future_proof_object"
            ],
            "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
            "claim_ceiling": (
                "renormalized_expectation_domain_packet_only_no_assumption_"
                "discharge_no_conservation_witness_no_qft_gr_seam_closure"
            ),
            "failure_mode_if_unresolved": FAILURE_MODE_IF_UNRESOLVED,
        }

    accepted_prior_rows = result_review.get("accepted_renormalization_assumption_rows")
    acceptance_criteria = {
        "consumes_expected_rn_assump_002_result_review": result_review.get(
            "review_id"
        )
        == EXPECTED_ATTEMPT_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_ATTEMPT_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_ATTEMPT_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_ATTEMPT_RESULT_REVIEW_CLASSIFICATION,
        "result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": result_review.get("blocker")
        == BLOCKER,
        "preserves_renormalization_family": result_review.get(
            "selected_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY,
        "prior_operator_domain_family_accepted": result_review.get(
            "prior_completed_family"
        )
        == PRIOR_COMPLETED_FAMILY,
        "prior_rn_rows_accepted": accepted_prior_rows == ACCEPTED_PRIOR_ROWS,
        "source_renormalization_packet_available": renormalization_packet.get(
            "packet_id"
        )
        == EXPECTED_RENORMALIZATION_PACKET_ID,
        "selects_only_renormalized_expectation_domain_row": selected_row is not None
        and result_review.get("next_renormalization_assumption_row")
        == SELECTED_ROW_ID,
        "selected_row_status_tokens_current": selected_status
        == ["required", "missing", "candidate_reducible"],
        "renormalized_expectation_domain_object_recorded": bool(
            RENORMALIZED_EXPECTATION_DOMAIN
        ),
        "domain_boundary_recorded": len(DOMAIN_BOUNDARY) == 7,
        "prepares_reduction_analysis_only": bool(selected_row_payload),
        "does_not_discharge_renormalized_expectation_domain_assumption": True,
        "does_not_discharge_renormalization_assumptions": True,
        "does_not_construct_conservation_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_source_admissibility": result_review.get(
            "source_admissibility_claimed"
        )
        is False,
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
        else "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_renormalization_scope_assumption_reduction_attempt_result_review": (
            EXPECTED_ATTEMPT_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_renormalization_scope_assumption_reduction_attempt_result_review_pointer": _ptr(
            attempt_result_review_path
        ),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "source_renormalization_assumption_reduction_packet": (
            EXPECTED_RENORMALIZATION_PACKET_ID
        ),
        "source_renormalization_assumption_reduction_packet_pointer": _ptr(
            renormalization_packet_path
        ),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "prior_completed_family": PRIOR_COMPLETED_FAMILY,
        "prior_operator_domain_assumptions_accepted": True,
        "accepted_prior_renormalization_assumption_rows": ACCEPTED_PRIOR_ROWS,
        "accepted_prior_row_count": len(ACCEPTED_PRIOR_ROWS),
        "accepted_prior_renormalization_assumption_row": ACCEPTED_PRIOR_SCOPE_ROW,
        "selected_renormalization_assumption_row": SELECTED_ROW_ID,
        "selected_row_count": 1 if selected_row_payload else 0,
        "candidate_stress_energy_object": RENORMALIZED_STRESS_ENERGY_OBJECT,
        "renormalization_scope": RENORMALIZATION_SCOPE,
        "renormalized_expectation_domain": RENORMALIZED_EXPECTATION_DOMAIN,
        "renormalized_expectation_domain_object": RENORMALIZED_EXPECTATION_DOMAIN,
        "renormalized_expectation_domain_status": (
            RENORMALIZED_EXPECTATION_DOMAIN_STATUS
        ),
        "domain_boundary": DOMAIN_BOUNDARY,
        "renormalized_expectation_domain_assumption": selected_row_payload,
        "renormalized_expectation_domain_status_tokens": selected_status,
        "available_repo_evidence": selected_row_payload.get(
            "available_repo_evidence", []
        ),
        "required_future_proof_object": selected_row_payload.get(
            "required_future_proof_object", REQUIRED_FUTURE_PROOF_OBJECT
        ),
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "claim_ceiling": (
            "renormalized_expectation_domain_assumption_reduction_packet_"
            "preparation_only_no_assumption_discharge_no_conservation_witness_"
            "no_qft_gr_seam_closure"
        ),
        "failure_mode_if_unresolved": FAILURE_MODE_IF_UNRESOLVED,
        "renormalized_expectation_domain_assumption_reduction_analysis_prepared": (
            prepared
        ),
        "prepares_reduction_analysis_only": prepared,
        "renormalized_expectation_domain_assumption_discharged": False,
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_preparation": (
            False
        ),
        "renormalization_assumptions_discharged": False,
        "assumptions_reduced_or_discharged_by_preparation": False,
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
        else "REMEDIATE_QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_"
            "result_review_after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_"
            "PACKET_RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only RN-ASSUMP-003 renormalized-expectation-"
            "domain reduction analysis. It does not discharge the domain "
            "assumption or renormalization assumptions, construct a "
            "conservation proof object or conservation witness, claim source "
            "admissibility or Bianchi compatibility, derive the semiclassical "
            "Einstein equation, close QFT-GR, validate empirically, promote "
            "the master action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_renormalized_expectation_domain_assumption_reduction_packet(
    *,
    attempt_result_review_path: Path = DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    renormalization_packet_path: Path = DEFAULT_RENORMALIZATION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_renormalized_expectation_domain_assumption_reduction_packet(
        attempt_result_review_path=attempt_result_review_path,
        renormalization_packet_path=renormalization_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR renormalized-expectation-domain assumption-"
            "reduction packet."
        )
    )
    parser.add_argument(
        "--attempt-result-review",
        type=Path,
        default=DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    )
    parser.add_argument(
        "--renormalization-packet",
        type=Path,
        default=DEFAULT_RENORMALIZATION_PACKET_PATH,
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
    renormalization_packet_path = (
        ns.renormalization_packet
        if ns.renormalization_packet.is_absolute()
        else (REPO_ROOT / ns.renormalization_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_renormalized_expectation_domain_assumption_reduction_packet(
        attempt_result_review_path=attempt_result_review_path,
        renormalization_packet_path=renormalization_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_renormalized_expectation_domain_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} row={payload['selected_renormalization_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
