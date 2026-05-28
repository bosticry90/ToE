from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_candidate_source_domain_membership_assumption_reduction_packet_report import (
    CANDIDATE_SOURCE_OBJECT,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OPERATOR_DOMAIN_MEMBERSHIP_CONDITION,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIOR_ACCEPTED_ROW,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SELECTED_OPERATOR_ACTION_CONTRACT_ID,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_20260527_v0"
)
REVIEW_ID = (
    "QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_REDUCTION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_candidate_source_domain_membership_assumption_reduction_packet_"
    "result_review_accepts_packet_and_authorizes_bounded_reduction_attempt_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = (
    "execute_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt"
)

AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS = [
    "qft_gr_candidate_source_domain_membership_assumption_reduced_pending_result_review",
    (
        "qft_gr_candidate_source_domain_membership_assumption_obstruction_"
        "identified_requires_refinement"
    ),
    (
        "qft_gr_candidate_source_domain_membership_assumption_inconclusive_"
        "requires_assumption_reduction"
    ),
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_REDUCTION_PACKET_"
        "RESULT_REVIEW_20260527_v0.json"
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
                "The OD-ASSUMP-002 packet is accepted as preparation-only, so "
                "the next bounded step may attempt the candidate source-domain "
                "membership reduction without claiming source admissibility."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_state_expectation_domain_link_assumption_"
                "reduction_packet"
            ),
            "decision": "deferred",
            "reason": (
                "State-expectation domain linkage is OD-ASSUMP-003 and remains "
                "downstream of the candidate source-domain membership attempt."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_renormalized_expectation_domain_link_assumption_"
                "reduction_packet"
            ),
            "decision": "deferred",
            "reason": (
                "Renormalized-expectation domain linkage is OD-ASSUMP-004 and "
                "requires later row selection."
            ),
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": (
                "Accepting the source-domain membership packet does not "
                "authorize a conservation proof-object attempt."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "No packet result review closes QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is outside this bounded result review.",
        },
    ]


def build_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    selected_assumption = packet.get("candidate_source_domain_membership_assumption", {})
    selected_status = packet.get("candidate_source_domain_membership_status_tokens", [])
    candidate_next_targets = _candidate_next_targets()

    acceptance_criteria = {
        "consumes_expected_candidate_source_domain_membership_packet": packet.get(
            "packet_id"
        )
        == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": packet.get("blocker")
        == "insufficient_assumptions_for_conservation"
        and packet.get("selected_blocker") == "insufficient_assumptions_for_conservation",
        "preserves_operator_domain_family": packet.get("current_family")
        == PRIMARY_ASSUMPTION_FAMILY
        and packet.get("selected_assumption_family") == PRIMARY_ASSUMPTION_FAMILY
        and packet.get("primary_assumption_reduction_family")
        == PRIMARY_ASSUMPTION_FAMILY,
        "prior_row001_contract_remains_accepted": packet.get(
            "prior_accepted_operator_domain_assumption_row"
        )
        == PRIOR_ACCEPTED_ROW
        and packet.get("prior_accepted_selected_operator_action_contract")
        == SELECTED_OPERATOR_ACTION_CONTRACT_ID,
        "confirms_selected_row002": packet.get("selected_operator_domain_assumption_row")
        == SELECTED_ROW_ID
        and selected_assumption.get("assumption_id") == SELECTED_ROW_ID,
        "confirms_candidate_source_object": packet.get("candidate_source_object")
        == CANDIDATE_SOURCE_OBJECT
        and selected_assumption.get("candidate_source_object") == CANDIDATE_SOURCE_OBJECT,
        "confirms_operator_domain_membership_condition": packet.get(
            "operator_domain_membership_condition"
        )
        == OPERATOR_DOMAIN_MEMBERSHIP_CONDITION
        and selected_assumption.get("operator_domain_membership_condition")
        == OPERATOR_DOMAIN_MEMBERSHIP_CONDITION,
        "selected_row_status_tokens_current": selected_status
        == ["required", "missing", "candidate_reducible"],
        "selected_row_status_values_valid": all(
            status in ROW_STATUS_ENUM for status in selected_status
        ),
        "packet_preparation_only_confirmed": packet.get("prepared") is True
        and packet.get(
            "candidate_source_domain_membership_assumption_reduction_analysis_prepared"
        )
        is True
        and packet.get("assumptions_reduced_or_discharged_by_preparation") is False,
        "no_source_admissibility_claim": packet.get("source_admissibility_claimed")
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_proof_object_constructed": packet.get(
            "conservation_proof_object_constructed"
        )
        is False
        and packet.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": packet.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_bianchi_compatibility_claim": packet.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_derivation": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": packet.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": packet.get("empirical_validation_claimed") is False,
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
            "QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_REDUCTION_"
            "PACKET_RESULT_REVIEW_REJECTS_OR_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_candidate_source_domain_membership_assumption_reduction_"
            "packet_result_review_rejects_or_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_candidate_source_domain_membership_assumption_reduction_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "current_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "prior_accepted_operator_domain_assumption_row": PRIOR_ACCEPTED_ROW,
        "prior_accepted_selected_operator_action_contract": SELECTED_OPERATOR_ACTION_CONTRACT_ID,
        "prior_row001_contract_remains_accepted": accepted,
        "selected_operator_domain_assumption_row": SELECTED_ROW_ID,
        "candidate_source_domain_membership_assumption": selected_assumption,
        "candidate_source_domain_membership_status_tokens": selected_status,
        "candidate_source_object": CANDIDATE_SOURCE_OBJECT,
        "operator_domain_membership_condition": OPERATOR_DOMAIN_MEMBERSHIP_CONDITION,
        "packet_preparation_only_confirmed": accepted,
        "candidate_source_domain_membership_packet_accepted_by_review": accepted,
        "candidate_source_domain_membership_analysis_accepted": accepted,
        "candidate_source_domain_membership_assumption_discharged": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "assumptions_reduced_or_discharged_by_review": False,
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
        "bounded_reduction_attempt_authorized": accepted,
        "authorized_attempt_scope": (
            "candidate_source_domain_membership_assumption_reduction_attempt_only_"
            "no_source_admissibility_no_conservation_proof_object_no_qft_gr_seam_closure"
        ),
        "authorized_attempt_result_classifications": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
        "authorized_attempt_result_classification_count": len(
            AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_"
            "REDUCTION_PACKET_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_execution"
        ),
        "selected_route": (
            "qft_gr_candidate_source_domain_membership_assumption_reduction_"
            "attempt_after_packet_result_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_ASSUMPTION_"
            "REDUCTION_ATTEMPT_ONLY_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the OD-ASSUMP-002 candidate "
            "source-domain membership packet and authorizes one bounded "
            "reduction attempt. It does not claim source admissibility, "
            "construct a conservation proof object or conservation witness, "
            "claim Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, promote the master "
            "action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review(
            packet_path=packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR candidate source-domain membership "
            "assumption-reduction packet result review."
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
    payload = (
        write_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review(
            packet_path=packet_path,
            out=out,
            captured_at_utc=str(ns.captured_at_utc),
        )
    )
    print(
        "qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
