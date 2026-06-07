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
    OPERATOR_DOMAIN_COMPATIBILITY,
    PRIOR_COMPLETED_FAMILY,
    RENORMALIZED_EXPECTATION_DOMAIN,
    RENORMALIZED_STRESS_ENERGY_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    BOUNDED_OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_STATUS,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROWS,
    CANDIDATE_REDUCTION_ROUTE,
    FAILURE_MODE_IF_UNRESOLVED,
    OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES,
    OPERATOR_DOMAIN_COMPATIBILITY_STATUS,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ROW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0"
)
REVIEW_ID = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTS_REDUCED_OPERATOR_DOMAIN_"
    "COMPATIBILITY_AND_AUTHORIZES_RENORMALIZATION_ASSUMPTION_REDUCTION_"
    "CLOSEOUT_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_"
    "attempt_result_review_accepts_reduced_operator_domain_compatibility_and_"
    "authorizes_renormalization_assumption_reduction_closeout_preparation_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = "prepare_qft_gr_renormalization_assumption_reduction_closeout_packet"
NEXT_TARGET_KIND = "qft_gr_renormalization_assumption_reduction_closeout_packet_preparation"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
        "REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0.json"
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


def _row_ids(rows: list[dict[str, Any]]) -> list[str]:
    return [str(row.get("assumption_id")) for row in rows]


def _operator_domain_compatibility_nonclaims(prefix: str = "") -> dict[str, bool]:
    return {
        f"{prefix}operator_domain_compatibility_assumption_discharged": False,
        f"{prefix}operator_domain_compatibility_assumption_discharged_by_review": False,
        f"{prefix}operator_domain_compatibility_reduced_or_discharged_by_review": False,
        f"{prefix}operator_domain_compatibility_reduced_or_discharged_by_implication": False,
        f"{prefix}operator_domain_compatibility_discharged": False,
        f"{prefix}operator_domain_compatibility_discharged_by_implication": False,
        f"{prefix}operator_domain_compatibility_claimed_as_conservation_proof": False,
        f"{prefix}operator_domain_compatibility_claimed_as_conservation_source": False,
        f"{prefix}operator_domain_compatibility_claimed_as_source_admissibility": False,
        f"{prefix}operator_domain_compatibility_claimed_as_bianchi_compatibility": False,
    }


def _global_nonclaims() -> dict[str, bool]:
    return {
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "conservation_proved": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "assumption_discharge_claimed": False,
        "renormalization_assumptions_discharged_by_review": False,
        "renormalization_assumptions_reduced_or_discharged_by_review": False,
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


def _attempt_nonclaims() -> dict[str, bool]:
    return {
        "operator_domain_compatibility_assumption_discharged": False,
        "operator_domain_compatibility_assumption_discharged_by_attempt": False,
        "operator_domain_compatibility_reduced_or_discharged_by_attempt": False,
        "operator_domain_compatibility_reduced_or_discharged_by_implication": False,
        "operator_domain_compatibility_discharged": False,
        "operator_domain_compatibility_discharged_by_implication": False,
        "operator_domain_compatibility_claimed_as_conservation_proof": False,
        "operator_domain_compatibility_claimed_as_conservation_source": False,
        "operator_domain_compatibility_claimed_as_source_admissibility": False,
        "operator_domain_compatibility_claimed_as_bianchi_compatibility": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "conservation_proved": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "assumption_discharge_claimed": False,
        "assumptions_reduced_or_discharged_by_implication": False,
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


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The repo-authoritative renormalization row inventory ends at "
                "RN-ASSUMP-005, so accepting the bounded operator-domain "
                "compatibility reduction authorizes closeout packet preparation only."
            ),
        },
        {
            "target": "select_next_renormalization_assumption_row",
            "decision": "not_authorized",
            "reason": (
                "The current renormalization packet contains no candidate row after "
                "RN-ASSUMP-005."
            ),
        },
        {
            "target": (
                "discharge_qft_gr_renormalization_operator_domain_compatibility_"
                "assumption"
            ),
            "decision": "not_authorized",
            "reason": (
                "This result review accepts a bounded reduction contract only, not "
                "operator-domain compatibility discharge."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "The conservation blocker remains insufficient_assumptions_for_conservation.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized by this review.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The bounded compatibility contract is not a source-admissibility claim.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "The bounded compatibility contract is not a Bianchi-compatibility claim.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains outside this result review.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission remain unauthorized.",
        },
    ]


def _acceptance_criteria(
    attempt: dict[str, Any],
    row_ids: list[str],
    candidate_next_targets: list[dict[str, str]],
) -> dict[str, bool]:
    contract = attempt.get("operator_domain_compatibility_reduction_contract", {})
    attempt_selected_targets = _selected_targets(attempt.get("candidate_next_targets", []))
    expected_row_ids = [
        *ACCEPTED_PRIOR_ROWS,
        SELECTED_ROW_ID,
    ]
    return {
        "consumes_expected_attempt_artifact": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID
        and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
        and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME,
        "confirms_expected_attempt_classification": attempt.get("result_classification")
        == EXPECTED_ATTEMPT_CLASSIFICATION,
        "attempt_selected_this_result_review_target": attempt.get("selected_next_target")
        == CONSUMED_TARGET
        and attempt_selected_targets == [CONSUMED_TARGET],
        "attempt_executed_and_accepted": attempt.get("executed") is True
        and attempt.get("accepted") is True,
        "preserves_blocker_family_and_prior_family": attempt.get("selected_blocker")
        == BLOCKER
        and attempt.get("blocker") == BLOCKER
        and attempt.get("selected_assumption_family") == SELECTED_ASSUMPTION_FAMILY
        and attempt.get("prior_completed_family") == PRIOR_COMPLETED_FAMILY,
        "confirms_rn_assump_001_002_003_004_remain_accepted": attempt.get(
            "accepted_prior_renormalization_assumption_rows"
        )
        == ACCEPTED_PRIOR_ROWS,
        "confirms_selected_row005_only": attempt.get(
            "selected_renormalization_assumption_row"
        )
        == SELECTED_ROW_ID
        and contract.get("assumption_id") == SELECTED_ROW_ID,
        "confirms_operator_domain_compatibility_contract": contract.get("contract_id")
        == OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID
        and contract.get("contract_status")
        == BOUNDED_OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_STATUS
        and contract.get("candidate_stress_energy_object")
        == RENORMALIZED_STRESS_ENERGY_OBJECT
        and contract.get("renormalized_expectation_domain")
        == RENORMALIZED_EXPECTATION_DOMAIN
        and contract.get("operator_domain_compatibility")
        == OPERATOR_DOMAIN_COMPATIBILITY
        and contract.get("scope_boundaries") == OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES
        and contract.get("required_future_proof_object")
        == REQUIRED_FUTURE_PROOF_OBJECT
        and contract.get("candidate_reduction_route") == CANDIDATE_REDUCTION_ROUTE,
        "confirms_reduced_pending_review_result": attempt.get(
            "operator_domain_compatibility_assumption_reduced_pending_result_review"
        )
        is True
        and attempt.get("operator_domain_compatibility_assumption_reduced_by_attempt")
        is True
        and attempt.get("operator_domain_compatibility_assumption_obstruction_identified")
        is False
        and attempt.get("operator_domain_compatibility_assumption_inconclusive")
        is False,
        "preserves_attempt_nonclaim_boundary": all(
            attempt.get(key) is value for key, value in _attempt_nonclaims().items()
        ),
        "repo_authoritative_row_inventory_has_no_row_after_rn005": row_ids
        == expected_row_ids
        and row_ids[-1] == SELECTED_ROW_ID,
        "selects_exactly_one_closeout_preparation_target": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }


def build_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    renormalization_packet_path: Path = DEFAULT_RENORMALIZATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    renormalization_packet = _read_json(renormalization_packet_path)
    row_ids = _row_ids(renormalization_packet.get("candidate_reducible_assumptions", []))
    candidate_next_targets = _candidate_next_targets()
    criteria = _acceptance_criteria(attempt, row_ids, candidate_next_targets)
    accepted = all(criteria.values())
    selected_targets = _selected_targets(candidate_next_targets)
    selected_target = selected_targets[0] if selected_targets else None
    nonclaims = {
        **_operator_domain_compatibility_nonclaims(),
        **_global_nonclaims(),
    }

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
            "REDUCTION_ATTEMPT_RESULT_REVIEW_BLOCKED"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_renormalization_operator_domain_compatibility_assumption_"
            "reduction_attempt_result_review_blocked"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_pointer": _ptr(
            attempt_path
        ),
        "source_renormalization_assumption_reduction_packet": renormalization_packet.get(
            "packet_id"
        ),
        "source_renormalization_assumption_reduction_packet_pointer": _ptr(
            renormalization_packet_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_id": attempt.get("attempt_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_result_classification": attempt.get("result_classification"),
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
        "selected_renormalization_assumption_row": SELECTED_ROW_ID,
        "accepted_renormalization_assumption_row": SELECTED_ROW_ID,
        "accepted_renormalization_assumption_rows": [
            *ACCEPTED_PRIOR_ROWS,
            SELECTED_ROW_ID,
        ],
        "accepted_renormalization_assumption_row_count": len(ACCEPTED_PRIOR_ROWS) + 1,
        "repo_authoritative_renormalization_row_inventory": row_ids,
        "repo_authoritative_renormalization_row_inventory_count": len(row_ids),
        "repo_authoritative_renormalization_row_inventory_exhausted": accepted,
        "no_next_renormalization_assumption_row_available": accepted,
        "next_renormalization_assumption_row": None,
        "candidate_stress_energy_object": RENORMALIZED_STRESS_ENERGY_OBJECT,
        "renormalized_expectation_domain": RENORMALIZED_EXPECTATION_DOMAIN,
        "operator_domain_compatibility": OPERATOR_DOMAIN_COMPATIBILITY,
        "operator_domain_compatibility_condition": OPERATOR_DOMAIN_COMPATIBILITY,
        "operator_domain_compatibility_status": OPERATOR_DOMAIN_COMPATIBILITY_STATUS,
        "scope_boundaries": OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES,
        "operator_domain_compatibility_reduction_contract": attempt.get(
            "operator_domain_compatibility_reduction_contract"
        ),
        "accepted_contract_id": OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID,
        "bounded_operator_domain_compatibility_contract_status": (
            BOUNDED_OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_STATUS
        ),
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "failure_mode_if_unresolved": FAILURE_MODE_IF_UNRESOLVED,
        "operator_domain_compatibility_assumption_reduction_attempt_result_reviewed": (
            accepted
        ),
        "operator_domain_compatibility_assumption_reduction_accepted": accepted,
        "operator_domain_compatibility_assumption_reduction_rejected": not accepted,
        "operator_domain_compatibility_assumption_reduced_pending_result_review_accepted": (
            accepted
        ),
        "renormalization_assumption_reduction_closeout_packet_authorized": accepted,
        "renormalization_assumption_reduction_closeout_preparation_only": accepted,
        "renormalization_assumption_reduction_closeout_target": selected_target,
        **nonclaims,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_target
        if accepted
        else (
            "REMEDIATE_QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_"
            "ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_route": (
            "qft_gr_renormalization_assumption_reduction_closeout_packet_"
            "preparation_after_final_row_result_review"
        ),
        "selected_next_authorization_token": OUTCOME_ID if accepted else "",
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": len(selected_targets) if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_"
            "PACKET_ONLY_NO_OPERATOR_DOMAIN_COMPATIBILITY_DISCHARGE_"
            "CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": criteria,
        "non_claim_boundary": (
            "This result review accepts only the bounded RN-ASSUMP-005 "
            "operator-domain compatibility reduction contract and authorizes "
            "renormalization assumption-reduction closeout packet preparation. "
            "It does not discharge operator-domain compatibility, construct a "
            "conservation proof object or conservation witness, claim source "
            "admissibility or Bianchi compatibility, derive the semiclassical "
            "Einstein equation, close QFT-GR, validate empirically, promote the "
            "master action, assemble release, or authorize public submission."
        ),
        "claim_ceiling": [
            "no operator-domain compatibility discharge",
            "no conservation proof object",
            "no conservation witness",
            "no source admissibility",
            "no Bianchi compatibility",
            "no semiclassical Einstein equation",
            "no QFT-GR seam closure",
            "no empirical validation",
            "no master-action promotion",
            "no release assembly",
            "no public submission",
        ],
    }


def write_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    renormalization_packet_path: Path = DEFAULT_RENORMALIZATION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        renormalization_packet_path=renormalization_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR RN-ASSUMP-005 operator-domain compatibility "
            "assumption-reduction attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
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
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    renormalization_packet_path = (
        ns.renormalization_packet
        if ns.renormalization_packet.is_absolute()
        else (REPO_ROOT / ns.renormalization_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        renormalization_packet_path=renormalization_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
