from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    FINITENESS_REGULARITY_BOUNDARY,
    PRIOR_COMPLETED_FAMILY,
    RENORMALIZATION_SCOPE,
    RENORMALIZED_EXPECTATION_DOMAIN,
    RENORMALIZED_STRESS_ENERGY_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    BOUNDED_DOMAIN_CONTRACT_STATUS,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RENORMALIZED_EXPECTATION_DOMAIN_CONTRACT_ID,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROWS,
    DOMAIN_BOUNDARY,
    RENORMALIZED_EXPECTATION_DOMAIN_STATUS,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ROW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_20260606_v0"
)
REVIEW_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_"
    "RESULT_REVIEW_ACCEPTS_REDUCED_RENORMALIZED_EXPECTATION_DOMAIN_AND_"
    "AUTHORIZES_NEXT_RENORMALIZATION_ROW_SELECTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_"
    "result_review_accepts_reduced_renormalized_expectation_domain_and_"
    "authorizes_next_renormalization_row_selection_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_ROW_ID = "RN-ASSUMP-004-finiteness_regular_boundary"
NEXT_ROW_OBJECT = FINITENESS_REGULARITY_BOUNDARY
NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT = FINITENESS_REGULARITY_BOUNDARY
NEXT_TARGET = (
    "prepare_qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet"
)
NEXT_ACTION_SCOPE = (
    "PREPARE_QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_"
    "PACKET_ONLY_NO_DOMAIN_DISCHARGE_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0.json"
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
            "status": "selected",
            "reason": (
                "RN-ASSUMP-004-finiteness_regular_boundary is the next "
                "repo-authoritative renormalization row after accepting the "
                "bounded RN-ASSUMP-003 domain reduction."
            ),
        },
        {
            "target": "discharge_qft_gr_renormalized_expectation_domain_assumption",
            "status": "not_authorized",
            "reason": (
                "The result review accepts a bounded reduction only, not final "
                "renormalized-expectation-domain discharge."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "status": "not_authorized",
            "reason": "The conservation blocker remains insufficient_assumptions_for_conservation.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "status": "not_authorized",
            "reason": "No conservation witness is constructed or authorized by this review.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "status": "not_authorized",
            "reason": "The accepted domain reduction is not a source-admissibility claim.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "status": "not_authorized",
            "reason": "Bianchi compatibility remains a future proof obligation.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "status": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "status": "not_authorized",
            "reason": "QFT-GR seam closure remains outside this bounded review.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "status": "not_authorized",
            "reason": "Release assembly and public submission remain unauthorized.",
        },
    ]


def _non_claim_boundary() -> dict[str, bool]:
    return {
        "renormalized_expectation_domain_assumption_discharged": False,
        "renormalized_expectation_domain_assumption_discharged_by_review": False,
        "renormalized_expectation_domain_discharged_by_implication": False,
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_review": False,
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_implication": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
    }


def _attempt_non_claim_boundary() -> dict[str, bool]:
    return {
        "renormalized_expectation_domain_assumption_discharged": False,
        "renormalized_expectation_domain_assumption_discharged_by_attempt": False,
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_attempt": False,
        "renormalized_expectation_domain_assumption_reduced_or_discharged_by_implication": False,
        "renormalized_expectation_domain_discharged_by_implication": False,
        "renormalized_expectation_domain_claimed_as_conservation_proof": False,
        "renormalized_expectation_domain_claimed_as_conservation_source": False,
        "renormalized_expectation_domain_claimed_as_source_admissibility": False,
        "renormalized_expectation_domain_claimed_as_bianchi_compatibility": False,
        "actual_conservation_claimed": False,
        "conservation_proved": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
    }


def _acceptance_criteria(attempt: dict[str, Any]) -> list[dict[str, Any]]:
    selected_targets = [
        entry.get("target")
        for entry in attempt.get("candidate_next_targets", [])
        if entry.get("decision") == "selected"
    ]
    contract = attempt.get("renormalized_expectation_domain_reduction_contract", {})
    attempt_nonclaims = _attempt_non_claim_boundary()
    return [
        {
            "criterion": "consumes_expected_attempt_artifact",
            "satisfied": attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID
            and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
            and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME,
        },
        {
            "criterion": "confirms_expected_attempt_classification",
            "satisfied": attempt.get("result_classification")
            == EXPECTED_ATTEMPT_CLASSIFICATION,
        },
        {
            "criterion": "attempt_selected_this_result_review_target",
            "satisfied": attempt.get("selected_next_target") == CONSUMED_TARGET
            and selected_targets == [CONSUMED_TARGET],
        },
        {
            "criterion": "preserves_blocker_family_and_row",
            "satisfied": attempt.get("blocker") == BLOCKER
            and attempt.get("selected_assumption_family") == SELECTED_ASSUMPTION_FAMILY
            and attempt.get("selected_renormalization_assumption_row") == SELECTED_ROW_ID,
        },
        {
            "criterion": "confirms_rn_assump_001_002_remain_accepted",
            "satisfied": attempt.get("accepted_prior_renormalization_assumption_rows")
            == ACCEPTED_PRIOR_ROWS,
        },
        {
            "criterion": "confirms_reduced_pending_result_review_classification",
            "satisfied": attempt.get(
                "renormalized_expectation_domain_assumption_reduced_pending_result_review"
            )
            is True
            and attempt.get(
                "renormalized_expectation_domain_assumption_reduced_by_attempt"
            )
            is True
            and attempt.get(
                "renormalized_expectation_domain_assumption_obstruction_identified"
            )
            is False
            and attempt.get("renormalized_expectation_domain_assumption_inconclusive")
            is False,
        },
        {
            "criterion": "preserves_bounded_domain_contract",
            "satisfied": contract.get("contract_id")
            == RENORMALIZED_EXPECTATION_DOMAIN_CONTRACT_ID
            and contract.get("contract_status") == BOUNDED_DOMAIN_CONTRACT_STATUS
            and contract.get("assumption_id") == SELECTED_ROW_ID
            and contract.get("renormalized_expectation_domain")
            == RENORMALIZED_EXPECTATION_DOMAIN
            and contract.get("domain_boundary") == DOMAIN_BOUNDARY,
        },
        {
            "criterion": "does_not_discharge_domain",
            "satisfied": attempt.get("renormalized_expectation_domain_assumption_discharged")
            is False
            and attempt.get(
                "renormalized_expectation_domain_assumption_discharged_by_attempt"
            )
            is False
            and attempt.get("renormalized_expectation_domain_discharged_by_implication")
            is False,
        },
        {
            "criterion": "preserves_nonclaim_boundary",
            "satisfied": all(
                attempt.get(key) is value for key, value in attempt_nonclaims.items()
            ),
        },
        {
            "criterion": "selects_exactly_one_next_target",
            "satisfied": len(
                [
                    entry
                    for entry in _candidate_next_targets()
                    if entry["status"] == "selected"
                ]
            )
            == 1
            and NEXT_TARGET
            == (
                "prepare_qft_gr_renormalized_expectation_finiteness_assumption_"
                "reduction_packet"
            ),
        },
    ]


def build_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    criteria = _acceptance_criteria(attempt)
    accepted = all(entry["satisfied"] for entry in criteria)
    nonclaims = _non_claim_boundary()
    candidate_next_targets = _candidate_next_targets()
    selected_targets = [
        entry["target"]
        for entry in candidate_next_targets
        if entry["status"] == "selected"
    ]

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accept" if accepted else "reject",
        "outcome_id": OUTCOME_ID,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "consumes_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt": (
            EXPECTED_ATTEMPT_ID
        ),
        "consumes_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_id": attempt.get("attempt_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_result_classification": attempt.get("result_classification"),
        "prior_completed_family": PRIOR_COMPLETED_FAMILY,
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "current_family": SELECTED_ASSUMPTION_FAMILY,
        "accepted_prior_renormalization_assumption_rows": ACCEPTED_PRIOR_ROWS,
        "selected_renormalization_assumption_row": SELECTED_ROW_ID,
        "accepted_renormalization_assumption_row": SELECTED_ROW_ID,
        "accepted_renormalization_assumption_rows": [
            *ACCEPTED_PRIOR_ROWS,
            SELECTED_ROW_ID,
        ],
        "next_renormalization_assumption_row": NEXT_ROW_ID,
        "next_renormalization_assumption_row_object": NEXT_ROW_OBJECT,
        "next_renormalization_assumption_row_required_future_proof_object": (
            NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT
        ),
        "candidate_stress_energy_object": RENORMALIZED_STRESS_ENERGY_OBJECT,
        "renormalization_scope": RENORMALIZATION_SCOPE,
        "renormalized_expectation_domain": RENORMALIZED_EXPECTATION_DOMAIN,
        "renormalized_expectation_domain_object": RENORMALIZED_EXPECTATION_DOMAIN,
        "renormalized_expectation_domain_reduction_contract": attempt.get(
            "renormalized_expectation_domain_reduction_contract"
        ),
        "accepted_contract_id": RENORMALIZED_EXPECTATION_DOMAIN_CONTRACT_ID,
        "bounded_domain_contract_status": BOUNDED_DOMAIN_CONTRACT_STATUS,
        "source_packet_domain_status": RENORMALIZED_EXPECTATION_DOMAIN_STATUS,
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "domain_boundary": DOMAIN_BOUNDARY,
        "renormalized_expectation_domain_assumption_reduction_attempt_result_reviewed": (
            accepted
        ),
        "renormalized_expectation_domain_assumption_reduction_accepted": accepted,
        "renormalized_expectation_domain_assumption_reduction_rejected": not accepted,
        "renormalized_expectation_domain_assumption_reduced_pending_result_review_accepted": (
            accepted
        ),
        **nonclaims,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_targets[0] if selected_targets else None,
        "selected_next_target_kind": (
            "qft_gr_renormalized_expectation_finiteness_assumption_reduction_packet_preparation"
        ),
        "selection_count": len(selected_targets),
        "next_action_scope": NEXT_ACTION_SCOPE,
        "acceptance_criteria": criteria,
        "non_claim_boundary": nonclaims,
        "claim_ceiling": [
            "no renormalized-expectation-domain discharge",
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
        "failure_mode_if_unresolved": (
            "renormalization-family progress remains blocked before the "
            "finiteness/regularity boundary row can be prepared"
        ),
    }


def write_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR RN-ASSUMP-003 renormalized-expectation-domain "
            "assumption-reduction attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
