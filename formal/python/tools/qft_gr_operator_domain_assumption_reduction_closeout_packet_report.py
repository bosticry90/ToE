from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_packet_report import (
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    PRIOR_ACCEPTED_ROW004,
    PRIOR_ACCEPTED_ROW005,
    SELECTED_ROW_ID as ACCEPTED_ROW006,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    PRIMARY_ASSUMPTION_FAMILY,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260527_v0"
PACKET_ID = "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
CLOSEOUT_CLASSIFICATION = (
    "qft_gr_operator_domain_assumption_reduction_closeout_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_operator_domain_assumption_reduction_closeout_packet_result"
)
BLOCKER = "insufficient_assumptions_for_conservation"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260527_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _accepted_rows() -> list[str]:
    return [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
        PRIOR_ACCEPTED_ROW004,
        PRIOR_ACCEPTED_ROW005,
        ACCEPTED_ROW006,
    ]


def _operator_domain_row_records() -> list[dict[str, str]]:
    sources = [
        "qft_gr_selected_operator_action_assumption_reduction_attempt_result_review_v0",
        "qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_v0",
        "qft_gr_state_expectation_domain_link_assumption_reduction_attempt_result_review_v0",
        "qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_v0",
        "qft_gr_conservation_form_scope_assumption_reduction_attempt_result_review_v0",
        "qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_v0",
    ]
    return [
        {
            "row_id": row,
            "status": "accepted",
            "source": source,
        }
        for row, source in zip(_accepted_rows(), sources, strict=True)
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The closeout packet is prepared and must be result-reviewed "
                "before any downstream conservation-proof, source-admissibility, "
                "Bianchi, or seam-closure action."
            ),
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": (
                "Operator-domain assumption-row closeout preparation does not "
                "construct or authorize a conservation proof object."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": (
                "No conservation witness is constructed or authorized by this "
                "closeout packet."
            ),
        },
        {
            "target": "prepare_qft_gr_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "reason": (
                "Operator-domain row closeout remains below source "
                "admissibility."
            ),
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": (
                "Accepted operator-domain rows do not imply Bianchi "
                "compatibility."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains explicitly unclaimed.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is outside this bounded checkpoint.",
        },
    ]


def build_qft_gr_operator_domain_assumption_reduction_closeout_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    accepted_rows = _accepted_rows()
    row_records = _operator_domain_row_records()
    candidate_next_targets = _candidate_next_targets()

    acceptance_criteria = {
        "consumes_expected_metric_connection_result_review": result_review.get(
            "schema_id"
        )
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID
        and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_selected_this_closeout_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "result_review_accepts_all_six_rows": result_review.get(
            "accepted_operator_domain_assumption_rows"
        )
        == accepted_rows,
        "operator_domain_family_reduced_upstream": result_review.get(
            "operator_domain_assumptions_reduced_for_this_lane"
        )
        is True
        and result_review.get("operator_domain_assumption_reduction_family_reduced")
        is True,
        "closeout_packet_authorized_upstream": result_review.get(
            "operator_domain_assumption_reduction_closeout_packet_authorized"
        )
        is True
        and result_review.get("operator_domain_assumption_reduction_closeout_target")
        == CONSUMED_TARGET,
        "blocker_preserved": result_review.get("blocker") == BLOCKER
        and result_review.get("selected_blocker") == BLOCKER,
        "family_preserved": result_review.get("selected_assumption_family")
        == PRIMARY_ASSUMPTION_FAMILY
        and result_review.get("primary_assumption_reduction_family")
        == PRIMARY_ASSUMPTION_FAMILY,
        "row_records_are_all_accepted": all(
            record["status"] == "accepted" for record in row_records
        )
        and len(row_records) == 6,
        "closeout_is_preparation_only": True,
        "no_conservation_proof": result_review.get("conservation_proved") is False
        and result_review.get("actual_conservation_claimed") is False,
        "no_conservation_proof_object_constructed": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed") is False,
        "no_conservation_witness_constructed": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_admissibility_claim": result_review.get(
            "source_admissibility_claimed"
        )
        is False
        and result_review.get("stress_energy_source_admissibility_claimed") is False,
        "no_bianchi_compatibility_claim": result_review.get(
            "Bianchi_compatibility_claimed"
        )
        is False,
        "no_semiclassical_einstein_derivation": result_review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": result_review.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": result_review.get("empirical_validation_claimed")
        is False,
        "no_master_action_promotion": result_review.get("master_action_promoted")
        is False
        and result_review.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": result_review.get(
            "release_assembly_authorized"
        )
        is False
        and result_review.get("release_packet_assembled") is False
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
        else "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_BLOCKED",
        "closeout_classification": CLOSEOUT_CLASSIFICATION
        if prepared
        else (
            "qft_gr_operator_domain_assumption_reduction_closeout_packet_blocked"
        ),
        "closeout_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "downstream_review_or_adjudication_required": True,
        "current_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "operator_domain_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "operator_domain_assumptions_row_sequence_completed": prepared,
        "operator_domain_assumption_row_count": 6,
        "accepted_operator_domain_assumption_row_count": 6,
        "accepted_operator_domain_assumption_rows": accepted_rows,
        "operator_domain_assumption_rows": row_records,
        "operator_domain_assumptions_reduced_for_this_lane": prepared,
        "operator_domain_assumption_reduction_family_reduced": prepared,
        "operator_domain_assumption_reduction_closeout_packet_authorized": prepared,
        "operator_domain_assumption_reduction_closeout_packet_prepared": prepared,
        "operator_domain_assumption_reduction_closeout_prepared": prepared,
        "operator_domain_assumption_reduction_closeout_status": (
            "prepared_pending_result_review" if prepared else "blocked"
        ),
        "operator_domain_assumption_reduction_closeout_result_review_required": prepared,
        "operator_domain_assumption_reduction_closeout_target": CONSUMED_TARGET,
        "operator_domain_assumption_reduction_closeout_packet_selected_next_target": (
            NEXT_TARGET if prepared else "REMEDIATE_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET"
        ),
        "operator_domain_assumption_reduction_closeout_preparation_only": prepared,
        "closeout_scope": (
            "operator_domain_assumption_reduction_closeout_packet_preparation_only_"
            "no_conservation_proof_object_no_conservation_witness_no_source_"
            "admissibility_no_bianchi_compatibility_no_qft_gr_seam_closure"
        ),
        "required_future_proof_object": (
            "conservation_proof_object_for_candidate_source_under_reduced_"
            "operator_domain_assumptions"
        ),
        "failure_mode_if_unresolved": (
            "operator-domain assumptions are row-level reduced but not yet "
            "accepted as a closeout packet, leaving the conservation blocker "
            "unadjudicated for downstream proof-object work"
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
        "assumption_discharge_claimed": False,
        "assumptions_discharged_by_closeout": False,
        "assumptions_reduced_or_discharged_by_closeout": False,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET",
        "selected_next_target_kind": (
            "qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_operator_domain_assumption_reduction_closeout_packet_result_"
            "review_after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_"
            "RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This closeout packet records only that OD-ASSUMP-001 through "
            "OD-ASSUMP-006 are accepted as row-level operator-domain "
            "assumption reductions for this lane. It preserves the blocker "
            "insufficient_assumptions_for_conservation and does not prove "
            "conservation, construct a conservation proof object or witness, "
            "claim source admissibility or Bianchi compatibility, derive the "
            "semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_operator_domain_assumption_reduction_closeout_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_operator_domain_assumption_reduction_closeout_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR operator-domain assumption-reduction "
            "closeout packet."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
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
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_operator_domain_assumption_reduction_closeout_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_operator_domain_assumption_reduction_closeout_packet_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
