from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_state_domain_object_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIOR_COMPLETED_FAMILIES,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_ROW_ID,
    STATE_ADMISSIBILITY_BOUNDARY,
    STATE_DOMAIN_OBJECT,
    STATE_DOMAIN_OBJECT_DEFINITION_STATUS,
    STATE_OBJECT_COMPATIBILITY_CONDITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "20260607_v0"
)
REVIEW_ID = "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "PACKET_AND_AUTHORIZES_BOUNDED_REDUCTION_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_domain_object_assumption_reduction_packet_result_review_accepts_"
    "packet_and_authorizes_bounded_reduction_attempt_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
NEXT_TARGET = "execute_qft_gr_state_domain_object_assumption_reduction_attempt"
AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS = [
    "qft_gr_state_domain_object_assumption_reduced_pending_result_review",
    "qft_gr_state_domain_object_assumption_obstruction_identified_requires_refinement",
    "qft_gr_state_domain_object_assumption_inconclusive_requires_assumption_reduction",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_20260607_v0.json"
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
                "The SD-ASSUMP-001 packet has been accepted; the next bounded "
                "step may attempt to reduce exactly the state-domain object "
                "assumption."
            ),
        },
        {
            "target": "prepare_qft_gr_state_admissibility_boundary_assumption_reduction_packet",
            "decision": "deferred",
            "reason": (
                "State admissibility boundary remains downstream of the "
                "SD-ASSUMP-001 bounded reduction attempt."
            ),
        },
        {
            "target": "prepare_qft_gr_state_expectation_compatibility_assumption_reduction_packet",
            "decision": "deferred",
            "reason": (
                "State-expectation compatibility remains downstream of the "
                "selected state-domain object row."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "Packet review does not construct a conservation proof object.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "Packet review does not construct a conservation witness.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "A state-domain object review does not claim source admissibility.",
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
            "reason": "QFT-GR seam closure remains outside this review.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission remain unauthorized.",
        },
    ]


def build_qft_gr_state_domain_object_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    selected_next_target_count = sum(
        1 for row in candidate_next_targets if row["decision"] == "selected"
    )
    selected_status = packet.get("state_domain_object_status_tokens", [])

    acceptance_criteria = {
        "consumes_expected_sd_assump_001_packet": packet.get("packet_id")
        == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": packet.get("blocker")
        == BLOCKER
        and packet.get("selected_blocker") == BLOCKER
        and packet.get("conservation_blocker_remains") is True,
        "preserves_state_domain_family": packet.get("selected_assumption_family")
        == SELECTED_ASSUMPTION_FAMILY
        and packet.get("primary_assumption_reduction_family")
        == SELECTED_ASSUMPTION_FAMILY,
        "confirms_completed_prior_families": packet.get(
            "completed_prior_assumption_families"
        )
        == PRIOR_COMPLETED_FAMILIES
        and packet.get("completed_prior_assumption_family_count")
        == len(PRIOR_COMPLETED_FAMILIES),
        "confirms_selected_row": packet.get("selected_state_domain_assumption_row")
        == SELECTED_ROW_ID
        and packet.get("selected_row_count") == 1,
        "selected_row_status_tokens_current": selected_status
        == ["required", "supplied", "candidate_reducible"],
        "state_domain_object_recorded": packet.get("state_domain_object")
        == STATE_DOMAIN_OBJECT,
        "state_admissibility_boundary_recorded_without_discharge": packet.get(
            "state_admissibility_boundary"
        )
        == STATE_ADMISSIBILITY_BOUNDARY,
        "state_object_compatibility_condition_recorded": packet.get(
            "state_object_compatibility_condition"
        )
        == STATE_OBJECT_COMPATIBILITY_CONDITION,
        "definition_status_records_not_final": packet.get(
            "state_domain_object_definition_status"
        )
        == STATE_DOMAIN_OBJECT_DEFINITION_STATUS,
        "packet_preparation_only_confirmed": packet.get("prepared") is True
        and packet.get("state_domain_object_assumption_reduction_analysis_prepared")
        is True
        and packet.get("prepares_reduction_analysis_only") is True,
        "no_state_domain_object_assumption_reduced_by_review": packet.get(
            "state_domain_object_assumption_discharged"
        )
        is False
        and packet.get("state_domain_object_assumption_reduced_or_discharged_by_preparation")
        is False
        and packet.get("state_domain_assumptions_discharged") is False,
        "no_conservation_proof_object_or_witness": packet.get(
            "conservation_proof_object_constructed"
        )
        is False
        and packet.get("proof_object_constructed") is False
        and packet.get("conservation_witness_constructed") is False,
        "no_source_admissibility_or_bianchi": packet.get(
            "source_admissibility_claimed"
        )
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False
        and packet.get("Bianchi_compatibility_claimed") is False,
        "no_semiclassical_einstein_derivation": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": packet.get("qft_gr_seam_closed") is False,
        "no_empirical_validation_or_master_action_promotion": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("scientific_validation_claimed") is False
        and packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": packet.get("release_assembly_authorized")
        is False
        and packet.get("release_packet_assembled") is False
        and packet.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": selected_next_target_count == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    accepted = all(bool(value) for value in acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_state_domain_object_assumption_reduction_packet_result_"
            "review_blocked"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_state_domain_object_assumption_reduction_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_state_domain_object_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_state_domain_assumption_row": SELECTED_ROW_ID,
        "selected_row_count": 1 if accepted else 0,
        "state_domain_object": STATE_DOMAIN_OBJECT,
        "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY,
        "state_object_compatibility_condition": STATE_OBJECT_COMPATIBILITY_CONDITION,
        "state_domain_object_definition_status": (
            STATE_DOMAIN_OBJECT_DEFINITION_STATUS
        ),
        "state_domain_object_status_tokens": selected_status,
        "packet_preparation_only_confirmed": accepted,
        "state_domain_object_assumption_discharged": False,
        "state_domain_object_assumption_reduced_by_review": False,
        "state_domain_object_assumption_reduced_or_discharged_by_review": False,
        "state_domain_assumptions_discharged_by_review": False,
        "state_domain_assumptions_reduced_or_discharged_by_review": False,
        "state_admissibility_discharged": False,
        "state_admissibility_claimed_as_source_admissibility": False,
        "bounded_reduction_attempt_authorized": accepted,
        "bounded_reduction_attempt_executed": False,
        "authorized_attempt_scope": (
            "state_domain_object_assumption_reduction_attempt_only_no_state_"
            "admissibility_discharge_no_conservation_witness_no_qft_gr_seam_"
            "closure"
        ),
        "authorized_attempt_result_classifications": (
            AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS
        ),
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
        if accepted
        else (
            "REMEDIATE_QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_PACKET_"
            "RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "qft_gr_state_domain_object_assumption_reduction_attempt_execution"
        ),
        "selected_route": (
            "qft_gr_state_domain_object_assumption_reduction_attempt_after_"
            "packet_result_review"
        ),
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": selected_next_target_count if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_STATE_DOMAIN_OBJECT_ASSUMPTION_REDUCTION_ATTEMPT_"
            "ONLY_NO_STATE_ADMISSIBILITY_DISCHARGE_CONSERVATION_WITNESS_OR_"
            "QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the SD-ASSUMP-001 packet and "
            "authorizes one bounded reduction attempt. It does not reduce or "
            "discharge the state-domain object assumption by review alone, "
            "construct a conservation proof object or conservation witness, "
            "claim source admissibility or Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_state_domain_object_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_state_domain_object_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR SD-ASSUMP-001 state-domain object "
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
    payload = write_qft_gr_state_domain_object_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_state_domain_object_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} row={payload['selected_state_domain_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
