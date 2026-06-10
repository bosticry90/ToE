from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    BOUNDED_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_STATUS,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_"
    "ATTEMPT_RESULT_REVIEW_20260609_v0"
)
REVIEW_ID = "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0"
OUTCOME_ID = "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTS_REDUCED_MR_ASSUMP_004_AND_AUTHORIZES_NEXT_MATHEMATICAL_REGULARITY_ROW_SELECTION_ONLY"
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_"
    "attempt_result_review_accepts_reduced_mr_assump_004_and_authorizes_next_"
    "mathematical_regularity_row_selection_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = "select_next_qft_gr_mathematical_regularity_row_from_repo_authoritative_inventory"
NEXT_TARGET_KIND = "qft_gr_mathematical_regularity_repo_authoritative_row_selection"
NEXT_ROW_ID = "NO_REPO_AUTHORITATIVE_MR_ROW_AFTER_MR_ASSUMP_004"
NEXT_ROW_OBJECT = "no_repo_authoritative_mathematical_regularity_row_after_mr_assump_004"
NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT = (
    "select_next_repo_authoritative_mathematical_regularity_row_before_any_"
    "conservation_claim"
)
LIMIT_INTERCHANGE_CONTRACT_STATUS_TOKEN_LITERAL = "bounded_repo_local_limit_interchange_regularization_boundary_contract_pending_result_review_not_limit_interchange_proof_or_conservation_discharge"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_ASSUMPTION_REDUCTION_"
        "ATTEMPT_RESULT_REVIEW_20260609_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, Any]]) -> list[str]:
    return [str(row.get("target")) for row in rows if row.get("decision") == "selected"]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "MR-ASSUMP-004 is the current terminal repo-authoritative "
                "mathematical-regularity row; select the next authoritative "
                "mathematical-regularity row before any conservation-proof branch."
            ),
        },
        {
            "target": "discharge_qft_gr_limit_interchange_regularization_boundary_assumption",
            "decision": "not_authorized",
            "reason": "Bounded row reduction is accepted; no global limit-interchange discharge is authorized.",
        },
        {
            "target": "discharge_qft_gr_mathematical_regularity_assumptions",
            "decision": "not_authorized",
            "reason": "Accepting MR-ASSUMP-004 does not discharge the entire family.",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "No conservation proof object is authorized by this result review.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is authorized by this result review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure is outside this checkpoint.",
        },
    ]


def _global_nonclaims() -> dict[str, bool]:
    return {
        "limit_interchange_regularization_boundary_assumption_discharged": False,
        "limit_interchange_regularization_boundary_assumption_discharged_by_review": False,
        "limit_interchange_regularization_boundary_assumption_reduced_or_discharged_by_review": False,
        "limit_interchange_regularization_boundary_reduced_or_discharged_by_implication": False,
        "mathematical_regularity_assumptions_discharged": False,
        "mathematical_regularity_assumptions_reduced_or_discharged_by_review": False,
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
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
    }


def _attempt_nonclaims() -> dict[str, bool]:
    return {
        "limit_interchange_regularization_boundary_assumption_discharged": False,
        "limit_interchange_regularization_boundary_assumption_discharged_by_attempt": False,
        "limit_interchange_regularization_boundary_assumption_reduced_or_discharged_by_implication": False,
        "limit_interchange_regularization_boundary_proved": False,
        "limit_interchange_regularization_boundary_proved_by_attempt": False,
        "mathematical_regularity_assumptions_discharged": False,
        "mathematical_regularity_assumptions_reduced_or_discharged_by_attempt": False,
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
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
    }


def _acceptance_criteria(attempt: dict[str, Any], packet: dict[str, Any]) -> dict[str, bool]:
    selected_attempt_targets = _selected_targets(attempt.get("candidate_next_targets", []))
    candidate_next_targets = _candidate_next_targets()
    selected_review_targets = _selected_targets(candidate_next_targets)
    contract = attempt.get("limit_interchange_regularization_boundary_reduction_contract", {})
    rows = packet.get("candidate_reducible_assumptions", [])
    row_ids = [row.get("assumption_id") for row in rows]
    attempt_nonclaims = _attempt_nonclaims()
    return {
        "consumes_expected_attempt_artifact": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID
        and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
        and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME,
        "confirms_expected_attempt_classification": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "attempt_selected_this_result_review_target": attempt.get("selected_next_target")
        == CONSUMED_TARGET
        and selected_attempt_targets == [CONSUMED_TARGET],
        "preserves_blocker_family_and_row": attempt.get("blocker") == BLOCKER
        and attempt.get("selected_assumption_family") == SELECTED_ASSUMPTION_FAMILY
        and attempt.get("selected_bounded_mathematical_regularity_assumption_row")
        == "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        "confirms_mr_assump_004_reduced_pending_review": attempt.get(
            "limit_interchange_regularization_boundary_assumption_reduced_pending_result_review"
        )
        is True
        and attempt.get("limit_interchange_regularization_boundary_assumption_reduced_by_attempt")
        is True
        and attempt.get("limit_interchange_regularization_boundary_assumption_obstruction_identified")
        is False
        and attempt.get("limit_interchange_regularization_boundary_assumption_inconclusive")
        is False,
        "preserves_bounded_limit_interchange_contract": contract.get("contract_id")
        == LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID
        and contract.get("contract_status")
        == BOUNDED_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_STATUS
        and contract.get("assumption_id")
        == "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        "preserves_attempt_nonclaim_boundary": all(
            attempt.get(key) is value for key, value in attempt_nonclaims.items()
        ),
        "no_repo_authoritative_row_after_mr_assump_004": (
            "MR-ASSUMP-004-limit_interchange_regularization_boundary" in row_ids
            and row_ids.index("MR-ASSUMP-004-limit_interchange_regularization_boundary")
            == len(row_ids) - 1
        ),
        "selects_exactly_one_next_target": selected_review_targets == [NEXT_TARGET],
    }


def build_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    packet = _read_json(packet_path)
    criteria = _acceptance_criteria(attempt, packet)
    accepted = all(criteria.values())
    nonclaims = _global_nonclaims()
    candidate_next_targets = _candidate_next_targets()
    selected_targets = _selected_targets(candidate_next_targets)

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accept" if accepted else "reject",
        "outcome_id": OUTCOME_ID,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "consumes_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt": EXPECTED_ATTEMPT_ID,
        "consumes_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_pointer": _ptr(
            attempt_path
        ),
        "source_mathematical_regularity_assumption_reduction_packet": packet.get("packet_id"),
        "source_mathematical_regularity_assumption_reduction_packet_pointer": _ptr(packet_path),
        "consumed_target": CONSUMED_TARGET,
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_id": attempt.get("attempt_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_result_classification": attempt.get("result_classification"),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "conservation_blocker_remains": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "current_family": SELECTED_ASSUMPTION_FAMILY,
        "accepted_mathematical_regularity_assumption_row": "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        "accepted_mathematical_regularity_assumption_rows": [
            "MR-ASSUMP-004-limit_interchange_regularization_boundary"
        ],
        "accepted_mathematical_regularity_assumption_row_count": 1,
        "selected_mathematical_regularity_assumption_row": "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        "limit_interchange_regularization_boundary_reduction_contract": attempt.get(
            "limit_interchange_regularization_boundary_reduction_contract"
        ),
        "accepted_contract_id": LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID,
        "bounded_limit_interchange_regularization_boundary_contract_status": (
            BOUNDED_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_STATUS
        ),
        "bounded_limit_interchange_regularization_boundary_contract_status_token_literal": (
            LIMIT_INTERCHANGE_CONTRACT_STATUS_TOKEN_LITERAL
        ),
        "limit_interchange_regularization_boundary_assumption_reduction_attempt_result_reviewed": accepted,
        "limit_interchange_regularization_boundary_assumption_reduction_accepted": accepted,
        "limit_interchange_regularization_boundary_assumption_reduction_rejected": not accepted,
        "limit_interchange_regularization_boundary_assumption_reduced_pending_result_review_accepted": accepted,
        "next_mathematical_regularity_assumption_row": NEXT_ROW_ID,
        "next_mathematical_regularity_assumption_row_object": NEXT_ROW_OBJECT,
        "next_mathematical_regularity_assumption_row_required_future_proof_object": NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT,
        "remaining_mathematical_regularity_assumption_rows": [],
        **nonclaims,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_targets[0] if selected_targets else None,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_authorization_token": OUTCOME_ID,
        "selection_count": len(selected_targets),
        "next_action_scope": (
            "SELECT_NEXT_QFT_GR_MATHEMATICAL_REGULARITY_ROW_FROM_REPO_"
            "AUTHORITATIVE_INVENTORY_ONLY_NO_CONSERVATION_PROOF_OBJECT_OR_"
            "QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": criteria,
        "non_claim_boundary": nonclaims,
        "claim_ceiling": [
            "no global limit-interchange regularization-boundary solve",
            "no mathematical-regularity family discharge",
            "no conservation proof object",
            "no conservation witness",
            "no state admissibility",
            "no source admissibility",
            "no Bianchi compatibility",
            "no semiclassical Einstein equation",
            "no QFT-GR seam closure",
            "no release assembly",
            "no public submission",
        ],
        "failure_mode_if_unresolved": (
            "next mathematical-regularity row selection remains unresolved before any "
            "conservation-proof branch can be authorized"
        ),
    }


def write_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR MR-ASSUMP-004 limit-interchange regularization-"
            "boundary assumption-reduction attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

