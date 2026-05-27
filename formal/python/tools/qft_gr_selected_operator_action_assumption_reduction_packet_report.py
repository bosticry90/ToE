from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    PACKET_ID as EXPECTED_OPERATOR_DOMAIN_PACKET_ID,
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_20260526_v0"
PACKET_ID = "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_"
    "NO_ASSUMPTION_DISCHARGE_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_selected_operator_action_assumption_reduction_packet_prepared_no_"
    "assumption_discharge_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
SELECTED_ROW_ID = SELECTED_OPERATOR_DOMAIN_ASSUMPTION_ROW
NEXT_TARGET = "review_qft_gr_selected_operator_action_assumption_reduction_packet_result"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_20260526_v0.json"
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
                "The selected-operator/action reduction packet must be reviewed "
                "before any assumption is reduced or discharged."
            ),
        },
        {
            "target": "prepare_qft_gr_candidate_source_domain_membership_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Candidate source-domain membership remains downstream of this packet review.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": "No conservation proof-object attempt is authorized by packet preparation.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Selected-operator/action analysis does not close QFT-GR.",
        },
    ]


def build_qft_gr_selected_operator_action_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    operator_domain_packet_path: Path = DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    operator_domain_packet = _read_json(operator_domain_packet_path)
    rows = operator_domain_packet.get("operator_domain_assumption_rows", [])
    selected_row = _row_by_id(rows, SELECTED_ROW_ID)
    candidate_next_targets = _candidate_next_targets()

    selected_row_payload: dict[str, Any] = {}
    if selected_row:
        selected_row_payload = {
            "assumption_id": selected_row["assumption_id"],
            "assumption_family": selected_row["assumption_family"],
            "current_status": selected_row["current_status"],
            "available_repo_evidence": selected_row["available_repo_evidence"],
            "required_future_proof_object": selected_row[
                "required_future_proof_object"
            ],
            "candidate_reduction_route": selected_row["reduction_route"],
            "claim_ceiling": (
                "selected_operator_action_assumption_reduction_packet_only_"
                "no_assumption_discharge"
            ),
            "failure_mode_if_unresolved": selected_row[
                "failure_mode_if_unresolved"
            ],
        }

    selected_status = selected_row_payload.get("current_status", [])
    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == "insufficient_assumptions_for_conservation",
        "preserves_operator_domain_family": result_review.get(
            "selected_assumption_family"
        )
        == PRIMARY_ASSUMPTION_FAMILY,
        "operator_domain_packet_available": operator_domain_packet.get("packet_id")
        == EXPECTED_OPERATOR_DOMAIN_PACKET_ID,
        "selects_only_selected_operator_action_row": selected_row is not None
        and result_review.get("selected_operator_domain_assumption_row")
        == SELECTED_ROW_ID,
        "selected_row_status_tokens_current": selected_status
        == ["required", "supplied", "missing", "candidate_reducible"],
        "selected_row_status_values_valid": all(
            status in ROW_STATUS_ENUM for status in selected_status
        ),
        "prepares_reduction_analysis_only": bool(selected_row_payload),
        "does_not_discharge_operator_action_assumption": True,
        "does_not_construct_conservation_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed") is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_source_or_bianchi": result_review.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and result_review.get("Bianchi_compatibility_claimed") is False,
        "does_not_derive_einstein_or_close_qft_gr": result_review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False
        and result_review.get("qft_gr_seam_closed") is False,
        "does_not_validate_or_promote": result_review.get(
            "empirical_validation_claimed"
        )
        is False
        and result_review.get("master_action_promoted") is False,
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
        else "QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_operator_domain_assumption_reduction_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_operator_domain_assumption_reduction_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "source_operator_domain_assumption_reduction_packet": EXPECTED_OPERATOR_DOMAIN_PACKET_ID,
        "source_operator_domain_assumption_reduction_packet_pointer": _ptr(
            operator_domain_packet_path
        ),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_operator_domain_assumption_row": SELECTED_ROW_ID,
        "selected_operator_action_assumption_reduction_analysis_prepared": prepared,
        "selected_operator_action_assumption": selected_row_payload,
        "selected_operator_action_assumption_status_tokens": selected_status,
        "row_status_enum": ROW_STATUS_ENUM,
        "selected_row_count": 1 if selected_row_payload else 0,
        "claim_ceiling": (
            "selected_operator_action_assumption_reduction_packet_only_no_"
            "assumption_discharge_no_conservation_witness_no_qft_gr_seam_closure"
        ),
        "operator_action_assumption_discharged": False,
        "assumptions_reduced_or_discharged_by_preparation": False,
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
        if prepared
        else "REMEDIATE_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_selected_operator_action_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_selected_operator_action_assumption_reduction_packet_result_"
            "review_after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_SELECTED_OPERATOR_ACTION_ASSUMPTION_REDUCTION_PACKET_"
            "RESULT_ONLY_NO_ASSUMPTION_DISCHARGE_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only selected-operator/action assumption "
            "reduction analysis. It does not discharge the operator/action "
            "assumption, construct a conservation proof object or conservation "
            "witness, claim source admissibility or Bianchi compatibility, "
            "derive the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_selected_operator_action_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    operator_domain_packet_path: Path = DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_selected_operator_action_assumption_reduction_packet(
        result_review_path=result_review_path,
        operator_domain_packet_path=operator_domain_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR selected-operator/action assumption-reduction packet."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument(
        "--operator-domain-packet",
        type=Path,
        default=DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    operator_domain_packet_path = (
        ns.operator_domain_packet
        if ns.operator_domain_packet.is_absolute()
        else (REPO_ROOT / ns.operator_domain_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_selected_operator_action_assumption_reduction_packet(
        result_review_path=result_review_path,
        operator_domain_packet_path=operator_domain_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_selected_operator_action_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} row={payload['selected_operator_domain_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
