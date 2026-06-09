from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_MATHEMATICAL_REGULARITY_PACKET_PATH,
    LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_MR002_RESULT_REVIEW_PATH,
    NEXT_ROW_ID as EXPECTED_SELECTED_ROW_ID,
    NEXT_ROW_OBJECT as EXPECTED_SELECTED_ROW_OBJECT,
    NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT as EXPECTED_REQUIRED_FUTURE_PROOF_OBJECT,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_MR002_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_MR002_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_MR002_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_MR002_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
    "20260609_v0"
)
PACKET_ID = (
    "QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_v0"
)
OUTCOME_ID = (
    "QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
    "PREPARED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet_"
    "prepared_with_no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
ACCEPTED_PRIOR_ROW_IDS = [
    "MR-ASSUMP-001-derivative_exchange_regular_boundary",
    "MR-ASSUMP-002-weak_strong_conservation_comparison_scope",
]
SELECTED_ROW_ID = EXPECTED_SELECTED_ROW_ID
SELECTED_ROW_OBJECT = EXPECTED_SELECTED_ROW_OBJECT
REQUIRED_FUTURE_PROOF_OBJECT = EXPECTED_REQUIRED_FUTURE_PROOF_OBJECT
NEXT_TARGET = (
    "review_qft_gr_distributional_pairing_regular_domain_assumption_reduction_"
    "packet_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet_"
    "result_review"
)
DISTRIBUTIONAL_PAIRING_DOMAIN_BOUNDARIES = [
    "distributional_pairing_domain_only_for_candidate_renormalized_expectation",
    "operator_domain_and_state_domain_assumption_rows_preserved",
    "weak_strong_scope_assumption_row_preserved_as_prior_reduction",
    "no_conservation_proof_object_claim",
    "no_conservation_witness_claim",
    "no_state_admissibility_claim",
    "no_source_admissibility_claim",
    "no_bianchi_compatibility_claim",
    "no_qft_gr_seam_closure",
]
CANDIDATE_REDUCTION_ROUTE = (
    "pin the regular domain for distributional pairings of the candidate "
    "renormalized stress-energy expectation"
)
FAILURE_MODE_IF_UNRESOLVED = (
    "the source candidate may be meaningful as an expectation but not regular "
    "enough for the distributional conservation form"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_"
        "20260609_v0.json"
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
                "The prepared MR-ASSUMP-003 packet must be result-reviewed before "
                "any bounded reduction attempt is authorized."
            ),
        },
        {
            "target": (
                "execute_qft_gr_distributional_pairing_regular_domain_assumption_"
                "reduction_attempt"
            ),
            "decision": "deferred",
            "reason": "A bounded MR-ASSUMP-003 attempt requires packet result review first.",
        },
        {
            "target": (
                "prepare_qft_gr_limit_interchange_regularization_boundary_"
                "assumption_reduction_packet"
            ),
            "decision": "deferred",
            "reason": "MR-ASSUMP-004 remains downstream of MR-ASSUMP-003 packet review.",
        },
        {
            "target": "prove_qft_gr_weak_conservation",
            "decision": "not_authorized",
            "reason": "Packet preparation does not prove weak conservation.",
        },
        {
            "target": "prove_qft_gr_strong_conservation",
            "decision": "not_authorized",
            "reason": "Packet preparation does not prove strong conservation.",
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
            "target": "claim_qft_gr_state_admissibility",
            "decision": "not_authorized",
            "reason": "Distributional pairing regular-domain preparation is not state admissibility.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "Distributional pairing regular-domain preparation is not source admissibility.",
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
        "distributional_pairing_regular_domain_assumption_discharged": False,
        "distributional_pairing_regular_domain_assumption_reduced_or_discharged_by_preparation": False,
        "mathematical_regularity_assumptions_discharged": False,
        "mathematical_regularity_assumptions_reduced_or_discharged_by_preparation": False,
        "weak_conservation_proved": False,
        "strong_conservation_proved": False,
        "weak_conservation_claimed": False,
        "strong_conservation_claimed": False,
        "state_admissibility_claimed": False,
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


def build_qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet(
    *,
    mr002_result_review_path: Path = DEFAULT_MR002_RESULT_REVIEW_PATH,
    mathematical_regularity_packet_path: Path = DEFAULT_MATHEMATICAL_REGULARITY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(mr002_result_review_path)
    mathematical_regularity_packet = _read_json(mathematical_regularity_packet_path)
    rows = mathematical_regularity_packet.get("candidate_reducible_assumptions", [])
    selected_row = _row_by_id(rows, SELECTED_ROW_ID)
    selected_status = selected_row.get("current_status", []) if selected_row else []
    candidate_next_targets = _candidate_next_targets()

    selected_row_payload: dict[str, Any] = {}
    if selected_row:
        selected_row_payload = {
            "assumption_id": selected_row["assumption_id"],
            "assumption_family": selected_row["assumption_family"],
            "current_status": selected_row["current_status"],
            "regularity_condition": selected_row["regularity_condition"],
            "distributional_pairing_regular_domain": SELECTED_ROW_OBJECT,
            "distributional_pairing_domain_boundaries": (
                DISTRIBUTIONAL_PAIRING_DOMAIN_BOUNDARIES
            ),
            "available_repo_evidence": selected_row["available_repo_evidence"],
            "required_future_proof_object": selected_row[
                "required_future_proof_object"
            ],
            "candidate_reduction_route": selected_row["candidate_reduction_route"],
            "claim_ceiling": (
                "distributional_pairing_regular_domain_packet_only_no_"
                "conservation_proof_no_conservation_witness_no_state_or_"
                "source_admissibility_no_bianchi_no_qft_gr_seam_closure"
            ),
            "failure_mode_if_unresolved": selected_row["failure_mode_if_unresolved"],
        }

    row_ids = [row.get("assumption_id") for row in rows]
    selected_index = row_ids.index(SELECTED_ROW_ID) if SELECTED_ROW_ID in row_ids else -1
    prior_index = (
        row_ids.index("MR-ASSUMP-002-weak_strong_conservation_comparison_scope")
        if "MR-ASSUMP-002-weak_strong_conservation_comparison_scope" in row_ids
        else -1
    )

    acceptance_criteria = {
        "consumes_expected_mr002_result_review": result_review.get("review_id")
        == EXPECTED_MR002_RESULT_REVIEW_ID,
        "mr002_result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_MR002_RESULT_REVIEW_SCHEMA_ID,
        "mr002_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_MR002_RESULT_REVIEW_OUTCOME,
        "mr002_result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_MR002_RESULT_REVIEW_CLASSIFICATION,
        "mr002_result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_mathematical_regularity_family": result_review.get(
            "selected_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY,
        "prior_assumption_families_remain_completed": result_review.get(
            "completed_prior_assumption_families"
        )
        == PRIOR_COMPLETED_FAMILIES,
        "accepted_prior_rows001002": ACCEPTED_PRIOR_ROW_IDS[1]
        in result_review.get("accepted_mathematical_regularity_assumption_rows", []),
        "selects_only_mr003": selected_row is not None
        and result_review.get("next_mathematical_regularity_assumption_row")
        == SELECTED_ROW_ID
        and selected_index == prior_index + 1,
        "selected_row_status_tokens_current": selected_status
        == ["required", "missing", "candidate_reducible"],
        "selected_row_object_expected": selected_row is not None
        and selected_row.get("regularity_condition") == SELECTED_ROW_OBJECT,
        "required_future_proof_object_recorded": selected_row_payload.get(
            "required_future_proof_object"
        )
        == REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route_recorded": selected_row_payload.get(
            "candidate_reduction_route"
        )
        == CANDIDATE_REDUCTION_ROUTE,
        "distributional_pairing_boundaries_recorded": selected_row_payload.get(
            "distributional_pairing_domain_boundaries"
        )
        == DISTRIBUTIONAL_PAIRING_DOMAIN_BOUNDARIES,
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == BLOCKER
        and result_review.get("conservation_blocker_remains") is True,
        "prepares_reduction_analysis_only": bool(selected_row_payload),
        "does_not_claim_conservation": result_review.get("conservation_proved") is False
        and result_review.get("actual_conservation_claimed") is False,
        "does_not_construct_conservation_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed") is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_state_or_source_admissibility": result_review.get(
            "state_admissibility_claimed"
        )
        is False
        and result_review.get("source_admissibility_claimed") is False
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
    nonclaims = _nonclaims()

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else (
            "QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_REDUCTION_"
            "PACKET_BLOCKED"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt_result_review": (
            EXPECTED_MR002_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt_result_review_pointer": _ptr(
            mr002_result_review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "source_mathematical_regularity_assumption_reduction_packet": (
            mathematical_regularity_packet.get("packet_id")
        ),
        "source_mathematical_regularity_assumption_reduction_packet_pointer": _ptr(
            mathematical_regularity_packet_path
        ),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "accepted_prior_mathematical_regularity_assumption_rows": ACCEPTED_PRIOR_ROW_IDS,
        "accepted_prior_mathematical_regularity_assumption_row_count": len(
            ACCEPTED_PRIOR_ROW_IDS
        ),
        "accepted_prior_mathematical_regularity_assumption_row": ACCEPTED_PRIOR_ROW_IDS[-1],
        "selected_mathematical_regularity_assumption_row": SELECTED_ROW_ID,
        "selected_bounded_mathematical_regularity_assumption_row": SELECTED_ROW_ID,
        "selected_row_count": 1 if selected_row_payload else 0,
        "selected_row_is_repo_authoritative_next_row": (
            selected_index == prior_index + 1
        ),
        "distributional_pairing_regular_domain_assumption": selected_row_payload,
        "distributional_pairing_regular_domain": SELECTED_ROW_OBJECT,
        "distributional_pairing_domain_boundaries": DISTRIBUTIONAL_PAIRING_DOMAIN_BOUNDARIES,
        "limit_interchange_regularization_boundary": LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY,
        "distributional_pairing_regular_domain_status_tokens": selected_status,
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
            "distributional_pairing_regular_domain_assumption_reduction_packet_"
            "preparation_only_no_conservation_proof_no_conservation_witness_no_"
            "state_or_source_admissibility_no_bianchi_no_qft_gr_seam_closure"
        ),
        "failure_mode_if_unresolved": selected_row_payload.get(
            "failure_mode_if_unresolved", FAILURE_MODE_IF_UNRESOLVED
        ),
        "distributional_pairing_regular_domain_assumption_reduction_analysis_prepared": (
            prepared
        ),
        "prepares_reduction_analysis_only": prepared,
        **nonclaims,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_"
            "ASSUMPTION_REDUCTION_PACKET"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_route": (
            "qft_gr_distributional_pairing_regular_domain_assumption_reduction_"
            "packet_result_review_after_preparation"
        ),
        "selected_next_authorization_token": OUTCOME_ID if prepared else "",
        "selection_count": 1 if prepared else 0,
        "selected_next_target_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN_ASSUMPTION_"
            "REDUCTION_PACKET_RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_"
            "QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only MR-ASSUMP-003 distributional pairing "
            "regular-domain reduction analysis. It preserves "
            "insufficient_assumptions_for_conservation and does not prove "
            "weak or strong conservation, construct a conservation proof "
            "object or witness, claim state/source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet(
    *,
    mr002_result_review_path: Path = DEFAULT_MR002_RESULT_REVIEW_PATH,
    mathematical_regularity_packet_path: Path = DEFAULT_MATHEMATICAL_REGULARITY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet(
        mr002_result_review_path=mr002_result_review_path,
        mathematical_regularity_packet_path=mathematical_regularity_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR MR-ASSUMP-003 distributional pairing regular "
            "domain assumption-reduction packet."
        )
    )
    parser.add_argument(
        "--mr002-result-review",
        type=Path,
        default=DEFAULT_MR002_RESULT_REVIEW_PATH,
    )
    parser.add_argument(
        "--mathematical-regularity-packet",
        type=Path,
        default=DEFAULT_MATHEMATICAL_REGULARITY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    mr002_result_review_path = (
        ns.mr002_result_review
        if ns.mr002_result_review.is_absolute()
        else (REPO_ROOT / ns.mr002_result_review)
    )
    mathematical_regularity_packet_path = (
        ns.mathematical_regularity_packet
        if ns.mathematical_regularity_packet.is_absolute()
        else (REPO_ROOT / ns.mathematical_regularity_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet(
        mr002_result_review_path=mr002_result_review_path,
        mathematical_regularity_packet_path=mathematical_regularity_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} "
        f"row={payload['selected_mathematical_regularity_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
