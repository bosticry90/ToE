"""Emit the QFT-GR RN-ASSUMP-001 attempt result-review packet."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.tools.qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    BOUNDED_OBJECT_CONTRACT_STATUS,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RENORMALIZED_STRESS_ENERGY_OBJECT_CONTRACT_ID,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_report import (
    CANDIDATE_REDUCTION_ROUTE,
    CANDIDATE_STRESS_ENERGY_OBJECT,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_renormalized_stress_energy_object_assumption_reduction_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    PRIOR_COMPLETED_FAMILY,
    RENORMALIZATION_SCOPE,
)

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_OUT = (
    ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0.json"
)

SCHEMA_ID = (
    "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0"
)
REVIEW_ID = "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_RENORMALIZED_STRESS_ENERGY_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_REDUCED_RENORMALIZED_STRESS_ENERGY_OBJECT_AND_AUTHORIZES_NEXT_RENORMALIZATION_ROW_SELECTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_result_review_"
    "accepts_reduced_renormalized_stress_energy_object_and_authorizes_next_renormalization_row_selection_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_ROW_ID = "RN-ASSUMP-002-renormalization_scope"
NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT = "bounded_renormalization_scope_defined_for_candidate_source"
NEXT_TARGET = "prepare_qft_gr_renormalization_scope_assumption_reduction_packet"
NEXT_ACTION_SCOPE = (
    "PREPARE_QFT_GR_RENORMALIZATION_SCOPE_ASSUMPTION_REDUCTION_PACKET_ONLY_"
    "NO_FINAL_OBJECT_DEFINITION_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "status": "selected",
            "reason": "first remaining renormalization row after RN-ASSUMP-001 acceptance",
        },
        {
            "target": "define_final_qft_gr_renormalized_stress_energy_object",
            "status": "not_authorized",
            "reason": "review accepts a bounded reduction result only, not a final object definition",
        },
        {
            "target": "discharge_qft_gr_renormalized_stress_energy_object_assumption",
            "status": "not_authorized",
            "reason": "review does not discharge the assumption by implication",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "status": "not_authorized",
            "reason": "blocker remains insufficient_assumptions_for_conservation",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "status": "not_authorized",
            "reason": "witness construction is outside this bounded result-review lane",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "status": "not_authorized",
            "reason": "source admissibility remains a future proof obligation",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "status": "not_authorized",
            "reason": "Bianchi compatibility is not established by this review",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "status": "not_authorized",
            "reason": "the QFT-GR scientific witness lane remains below derivation scope",
        },
        {
            "target": "close_qft_gr_seam",
            "status": "not_authorized",
            "reason": "the seam remains open until conservation/source/Bianchi obligations are met",
        },
        {
            "target": "authorize_qft_gr_public_submission",
            "status": "not_authorized",
            "reason": "release assembly and public submission remain outside scope",
        },
    ]


def _non_claim_boundary() -> dict[str, bool]:
    return {
        "renormalized_stress_energy_object_final_definition_claimed": False,
        "renormalized_stress_energy_object_defined_as_final": False,
        "renormalized_stress_energy_object_assumption_discharged": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "source_admissibility_claimed": False,
        "bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "release_assembly_authorized": False,
        "public_submission_authorized": False,
    }


def _attempt_non_claim_boundary() -> dict[str, bool]:
    return {
        "renormalized_stress_energy_object_final_definition_claimed": False,
        "renormalized_stress_energy_object_defined_as_final": False,
        "renormalized_stress_energy_object_assumption_discharged": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "source_admissibility_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "release_assembly_authorized": False,
        "public_submission_authorized": False,
    }


def _acceptance_criteria(attempt: dict[str, Any]) -> list[dict[str, Any]]:
    contract = attempt.get("renormalized_stress_energy_object_reduction_contract", {})
    selected_targets = [
        entry.get("target")
        for entry in attempt.get("candidate_next_targets", [])
        if entry.get("decision") == "selected"
    ]
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
            "satisfied": attempt.get("result_classification") == EXPECTED_ATTEMPT_CLASSIFICATION,
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
            "criterion": "confirms_reduced_pending_result_review_classification",
            "satisfied": attempt.get(
                "renormalized_stress_energy_object_assumption_reduced_pending_result_review"
            )
            is True
            and attempt.get("renormalized_stress_energy_object_assumption_reduced_by_attempt") is True
            and attempt.get("renormalized_stress_energy_object_assumption_obstruction_identified")
            is False
            and attempt.get("renormalized_stress_energy_object_assumption_inconclusive") is False,
        },
        {
            "criterion": "preserves_bounded_object_contract",
            "satisfied": contract.get("contract_id") == RENORMALIZED_STRESS_ENERGY_OBJECT_CONTRACT_ID
            and contract.get("definition_status") == BOUNDED_OBJECT_CONTRACT_STATUS
            and contract.get("renormalized_stress_energy_object") == CANDIDATE_STRESS_ENERGY_OBJECT,
        },
        {
            "criterion": "review_accepts_rn_assump_001_explicitly",
            "satisfied": attempt.get("selected_renormalization_assumption_row") == SELECTED_ROW_ID,
        },
        {
            "criterion": "does_not_define_or_discharge_final_object",
            "satisfied": attempt.get("renormalized_stress_energy_object_assumption_discharged") is False
            and attempt.get("renormalized_stress_energy_object_final_definition_claimed") is False
            and attempt.get("renormalized_stress_energy_object_defined_as_final") is False
            and attempt.get(
                "renormalized_stress_energy_object_final_definition_or_discharge_claimed_by_implication"
            )
            is False,
        },
        {
            "criterion": "preserves_nonclaim_boundary",
            "satisfied": all(attempt.get(key) is value for key, value in attempt_nonclaims.items()),
        },
        {
            "criterion": "selects_exactly_one_next_target",
            "satisfied": len([entry for entry in _candidate_next_targets() if entry["status"] == "selected"])
            == 1
            and NEXT_TARGET == "prepare_qft_gr_renormalization_scope_assumption_reduction_packet",
        },
    ]


def build_qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_result_review(
    attempt_path: Path,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _load_json(attempt_path)
    criteria = _acceptance_criteria(attempt)
    accepted = all(entry["satisfied"] for entry in criteria)
    nonclaims = _non_claim_boundary()
    candidate_next_targets = _candidate_next_targets()
    selected_targets = [entry["target"] for entry in candidate_next_targets if entry["status"] == "selected"]

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accept" if accepted else "reject",
        "outcome_id": OUTCOME_ID,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "consumes_qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt": str(
            attempt_path.as_posix()
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_id": attempt.get("attempt_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_result_classification": attempt.get("result_classification"),
        "prior_completed_family": PRIOR_COMPLETED_FAMILY,
        "blocker": BLOCKER,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_renormalization_assumption_row": SELECTED_ROW_ID,
        "accepted_renormalization_assumption_row": SELECTED_ROW_ID,
        "accepted_renormalization_assumption_rows": [SELECTED_ROW_ID],
        "next_renormalization_assumption_row": NEXT_ROW_ID,
        "next_renormalization_assumption_row_object": RENORMALIZATION_SCOPE,
        "next_renormalization_assumption_row_required_future_proof_object": (
            NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT
        ),
        "candidate_stress_energy_object": CANDIDATE_STRESS_ENERGY_OBJECT,
        "bounded_object_contract_status": BOUNDED_OBJECT_CONTRACT_STATUS,
        "accepted_contract_id": RENORMALIZED_STRESS_ENERGY_OBJECT_CONTRACT_ID,
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "candidate_reduction_route": CANDIDATE_REDUCTION_ROUTE,
        "renormalized_stress_energy_object_reduction_contract": attempt.get(
            "renormalized_stress_energy_object_reduction_contract"
        ),
        "renormalized_stress_energy_object_assumption_reduction_attempt_result_reviewed": accepted,
        "renormalized_stress_energy_object_assumption_reduction_accepted": accepted,
        "renormalized_stress_energy_object_assumption_reduction_rejected": not accepted,
        "renormalized_stress_energy_object_assumption_reduced_pending_result_review_accepted": (
            accepted
        ),
        "renormalized_stress_energy_object_assumption_discharged": False,
        "renormalized_stress_energy_object_assumption_discharged_by_review": False,
        "renormalized_stress_energy_object_final_definition_claimed_by_review": False,
        "renormalized_stress_energy_object_defined_as_final_by_review": False,
        "renormalized_stress_energy_object_final_definition_or_discharge_claimed_by_review": False,
        "renormalized_stress_energy_object_final_definition_or_discharge_claimed_by_implication": (
            False
        ),
        **nonclaims,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_targets[0] if selected_targets else None,
        "selected_next_target_kind": (
            "qft_gr_renormalization_scope_assumption_reduction_packet_preparation"
        ),
        "selection_count": len(selected_targets),
        "next_action_scope": NEXT_ACTION_SCOPE,
        "acceptance_criteria": criteria,
        "non_claim_boundary": nonclaims,
        "claim_ceiling": [
            "no final renormalized stress-energy object definition or discharge",
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
            "renormalization family cannot progress from object-contract reduction to scope reduction"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    payload = build_qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_result_review(
        args.attempt,
        args.captured_at_utc,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
