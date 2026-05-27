from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_result_review_report import (
    SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW,
)
from formal.python.tools.qft_gr_selected_operator_action_assumption_reduction_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "20260526_v0"
)
REVIEW_ID = (
    "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_SELECTED_OPERATOR_ACTION_ANALYSIS_AND_AUTHORIZES_BOUNDED_REDUCTION_"
    "ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_selected_operator_action_assumption_reduction_packet_result_review_"
    "accepts_selected_operator_action_analysis_and_authorizes_bounded_reduction_"
    "attempt_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
SELECTED_ROW_ID = SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW
NEXT_TARGET = "execute_qft_gr_selected_operator_action_assumption_reduction_attempt"

AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS = [
    "qft_gr_selected_operator_action_assumption_reduced_pending_result_review",
    "qft_gr_selected_operator_action_assumption_obstruction_identified_requires_refinement",
    "qft_gr_selected_operator_action_assumption_inconclusive_requires_assumption_reduction",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_20260526_v0.json"
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
                "The selected-operator/action packet has been accepted; the "
                "next bounded step may attempt to reduce exactly that one "
                "operator-domain assumption."
            ),
        },
        {
            "target": "prepare_qft_gr_candidate_source_domain_membership_assumption_reduction_packet",
            "decision": "deferred",
            "reason": (
                "Candidate source-domain membership remains downstream of the "
                "selected-operator/action reduction attempt."
            ),
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": (
                "A conservation proof-object attempt remains blocked until the "
                "bounded assumption-reduction chain is reviewed."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Selected-operator/action packet review does not close QFT-GR.",
        },
    ]


def build_qft_gr_selected_operator_action_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    selected_assumption = packet.get("selected_operator_action_assumption", {})
    candidate_next_targets = _candidate_next_targets()
    selected_status = packet.get("selected_operator_action_assumption_status_tokens", [])

    acceptance_criteria = {
        "consumes_expected_selected_operator_action_packet": packet.get("packet_id")
        == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": packet.get("selected_blocker")
        == "insufficient_assumptions_for_conservation"
        and packet.get("blocker") == "insufficient_assumptions_for_conservation",
        "preserves_operator_domain_family": packet.get("selected_assumption_family")
        == PRIMARY_ASSUMPTION_FAMILY
        and packet.get("primary_assumption_reduction_family")
        == PRIMARY_ASSUMPTION_FAMILY,
        "confirms_selected_row": packet.get("selected_operator_domain_assumption_row")
        == SELECTED_ROW_ID
        and selected_assumption.get("assumption_id") == SELECTED_ROW_ID,
        "selected_row_status_tokens_current": selected_status
        == ["required", "supplied", "missing", "candidate_reducible"],
        "selected_row_status_values_valid": all(
            status in ROW_STATUS_ENUM for status in selected_status
        ),
        "packet_preparation_only_confirmed": packet.get("prepared") is True
        and packet.get("selected_operator_action_assumption_reduction_analysis_prepared")
        is True,
        "no_assumption_discharged": packet.get("operator_action_assumption_discharged")
        is False
        and packet.get("assumptions_reduced_or_discharged_by_preparation")
        is False,
        "no_conservation_proof_object_constructed": packet.get(
            "conservation_proof_object_constructed"
        )
        is False
        and packet.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": packet.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_admissibility_or_bianchi_claim": packet.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and packet.get("Bianchi_compatibility_claimed") is False,
        "no_semiclassical_einstein_derivation": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": packet.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": packet.get("empirical_validation_claimed") is False,
        "no_master_action_promotion": packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": packet.get(
            "release_assembly_authorized"
        )
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
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_selected_operator_action_assumption_reduction_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_selected_operator_action_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_operator_domain_assumption_row": SELECTED_ROW_ID,
        "selected_operator_action_assumption_status_tokens": selected_status,
        "selected_operator_action_assumption": selected_assumption,
        "selected_operator_action_analysis_accepted": accepted,
        "packet_preparation_only_confirmed": accepted,
        "operator_action_assumption_discharged": False,
        "assumptions_reduced_or_discharged_by_review": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
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
        "bounded_reduction_attempt_authorized": accepted,
        "authorized_attempt_scope": (
            "selected_operator_action_assumption_reduction_attempt_only_no_"
            "conservation_proof_object_no_conservation_witness_no_qft_gr_seam_closure"
        ),
        "authorized_attempt_result_classifications": AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": (
            "qft_gr_selected_operator_action_assumption_reduction_attempt_execution"
        ),
        "selected_route": (
            "qft_gr_selected_operator_action_assumption_reduction_attempt_after_"
            "packet_result_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_ATTEMPT_"
            "ONLY_NO_CONSERVATION_PROOF_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the selected-operator/action "
            "assumption-reduction analysis and authorizes one bounded reduction "
            "attempt. It does not discharge the operator/action assumption, "
            "construct a conservation proof object or conservation witness, "
            "claim source admissibility or Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_selected_operator_action_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_selected_operator_action_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR selected-operator/action assumption-reduction "
            "packet result review."
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
        write_qft_gr_selected_operator_action_assumption_reduction_packet_result_review(
            packet_path=packet_path,
            out=out,
            captured_at_utc=str(ns.captured_at_utc),
        )
    )
    print(
        "qft_gr_selected_operator_action_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} row={payload['selected_operator_domain_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
