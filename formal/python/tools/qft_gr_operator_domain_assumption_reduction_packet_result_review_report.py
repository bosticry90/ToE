from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_20260526_v0"
REVIEW_ID = "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "OPERATOR_DOMAIN_REDUCTION_ANALYSIS_AND_AUTHORIZES_NEXT_BOUNDED_ASSUMPTION_"
    "TARGET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_operator_domain_assumption_reduction_packet_result_review_accepts_"
    "operator_domain_reduction_analysis_and_authorizes_next_bounded_assumption_"
    "target_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW = "OD-ASSUMP-001-selected_operator_action"
SELECTED_BOUNDED_ASSUMPTION_TARGET = (
    "prepare_qft_gr_selected_operator_action_assumption_reduction_packet"
)
NEXT_TARGET = SELECTED_BOUNDED_ASSUMPTION_TARGET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_20260526_v0.json"
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
            "assumption_id": SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW,
            "reason": (
                "The selected covariant derivative/operator action must be fixed "
                "before candidate source-domain membership can be reduced."
            ),
        },
        {
            "target": "prepare_qft_gr_candidate_source_domain_membership_assumption_reduction_packet",
            "decision": "deferred",
            "assumption_id": "OD-ASSUMP-002-candidate_source_domain_membership",
            "reason": "Source-domain membership depends on the selected operator action.",
        },
        {
            "target": "prepare_qft_gr_state_expectation_domain_link_assumption_reduction_packet",
            "decision": "deferred",
            "assumption_id": "OD-ASSUMP-003-state_expectation_domain_link",
            "reason": "State-expectation domain linkage remains downstream of operator-action selection.",
        },
        {
            "target": "prepare_qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet",
            "decision": "deferred",
            "assumption_id": "OD-ASSUMP-004-renormalized_expectation_domain_link",
            "reason": "Renormalized expectation domain linkage remains downstream of operator-action selection.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "assumption_id": "OD-NONRED-001-conservation-proof-object",
            "reason": "A proof-object attempt remains blocked until bounded assumption reduction is reviewed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "assumption_id": "OD-NONRED-005-qft-gr-seam-closure",
            "reason": "Operator-domain packet review does not close QFT-GR.",
        },
    ]


def _row_by_id(rows: list[dict[str, Any]], assumption_id: str) -> dict[str, Any] | None:
    for row in rows:
        if row.get("assumption_id") == assumption_id:
            return row
    return None


def build_qft_gr_operator_domain_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    rows = packet.get("operator_domain_assumption_rows", [])
    selected_row = _row_by_id(rows, SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW)
    candidate_next_targets = _candidate_next_targets()
    required_row_fields = {
        "assumption_id",
        "assumption_family",
        "current_status",
        "available_repo_evidence",
        "required_future_proof_object",
        "reduction_route",
        "claim_ceiling",
        "failure_mode_if_unresolved",
    }
    selected_row_status = selected_row.get("current_status", []) if selected_row else []
    acceptance_criteria = {
        "consumes_expected_operator_domain_packet": packet.get("packet_id")
        == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
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
        "all_operator_domain_rows_present": packet.get(
            "operator_domain_assumption_row_count"
        )
        == 6
        and isinstance(rows, list)
        and len(rows) == 6,
        "all_row_fields_present": all(required_row_fields <= set(row) for row in rows),
        "row_status_enum_present": packet.get("row_status_enum") == ROW_STATUS_ENUM,
        "row_status_values_valid": all(
            status in ROW_STATUS_ENUM for row in rows for status in row["current_status"]
        ),
        "selected_row_present": selected_row is not None,
        "selected_row_is_candidate_reducible": (
            "required" in selected_row_status
            and "candidate_reducible" in selected_row_status
        ),
        "confirms_packet_preparation_only": packet.get(
            "operator_domain_assumption_inventory_prepared"
        )
        is True
        and packet.get("operator_domain_assumption_reduction_analysis_prepared")
        is True,
        "no_assumption_discharged": packet.get(
            "assumptions_reduced_or_discharged_by_preparation"
        )
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
        else "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_operator_domain_assumption_reduction_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_operator_domain_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "operator_domain_assumption_rows_confirmed": accepted,
        "operator_domain_assumption_row_count": len(rows) if isinstance(rows, list) else 0,
        "row_status_enum": ROW_STATUS_ENUM,
        "selected_operator_domain_assumption_row": SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW,
        "selected_operator_domain_assumption_row_status": selected_row_status,
        "selected_operator_domain_assumption_row_reason": (
            "The selected operator/action is the first dependency because candidate "
            "source-domain membership, state-expectation linkage, and renormalized "
            "expectation linkage all depend on a fixed operator action."
        ),
        "selected_operator_domain_assumption_reduction_target": NEXT_TARGET,
        "packet_preparation_only_confirmed": accepted,
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
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": (
            "qft_gr_selected_operator_action_assumption_reduction_packet_preparation"
        ),
        "selected_route": (
            "qft_gr_selected_operator_action_assumption_reduction_packet_preparation_"
            "after_operator_domain_packet_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_"
            "ONLY_NO_ASSUMPTION_DISCHARGE_OR_CONSERVATION_WITNESS"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the operator-domain reduction analysis "
            "and selects the next bounded assumption target. It does not discharge "
            "assumptions, construct a conservation proof object or conservation "
            "witness, claim source admissibility or Bianchi compatibility, derive "
            "the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_operator_domain_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_operator_domain_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR operator-domain assumption-reduction packet result review."
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
    payload = write_qft_gr_operator_domain_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_operator_domain_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} row={payload['selected_operator_domain_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
