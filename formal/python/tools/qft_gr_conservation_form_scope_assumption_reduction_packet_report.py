from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_report import (
    CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_CONTRACT_ID,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_OUT as DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    PACKET_ID as EXPECTED_OPERATOR_DOMAIN_PACKET_ID,
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_report import (
    RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_selected_operator_action_assumption_reduction_attempt_report import (
    SELECTED_OPERATOR_ACTION_CONTRACT_ID,
)
from formal.python.tools.qft_gr_state_expectation_domain_link_assumption_reduction_attempt_report import (
    STATE_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_20260527_v0"
PACKET_ID = "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_conservation_form_scope_assumption_reduction_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
PRIOR_ACCEPTED_ROW001 = "OD-ASSUMP-001-selected_operator_action"
PRIOR_ACCEPTED_ROW002 = "OD-ASSUMP-002-candidate_source_domain_membership"
PRIOR_ACCEPTED_ROW003 = "OD-ASSUMP-003-state_expectation_domain_link"
PRIOR_ACCEPTED_ROW004 = "OD-ASSUMP-004-renormalized_expectation_domain_link"
SELECTED_ROW_ID = NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW
NEXT_TARGET = "review_qft_gr_conservation_form_scope_assumption_reduction_packet_result"
CONSERVATION_FORM_OPTIONS = ["weak", "strong", "distributional"]
SELECTED_BOUNDED_CONSERVATION_FORM = (
    "weak_operator_domain_covariant_divergence_zero_form"
)
REQUIRED_FUTURE_PROOF_OBJECT = (
    "bounded_weak_operator_domain_conservation_form_selected_for_future_proof_object"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_20260527_v0.json"
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


def _conservation_form_options() -> list[dict[str, str]]:
    return [
        {
            "form": "weak",
            "decision": "selected",
            "reason": (
                "Weak operator-domain conservation fixes the future proof-object "
                "scope without asserting pointwise conservation or importing "
                "distributional source admissibility."
            ),
        },
        {
            "form": "strong",
            "decision": "not_selected",
            "reason": (
                "Strong pointwise covariant-divergence conservation requires "
                "regularity and proof objects not available in this packet."
            ),
        },
        {
            "form": "distributional",
            "decision": "not_selected",
            "reason": (
                "Distributional conservation may be a later refinement, but this "
                "packet does not authorize distributional source admissibility."
            ),
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The conservation-form-scope packet must be reviewed before any "
                "bounded reduction attempt, conservation proof object, source "
                "admissibility question, or seam closure action."
            ),
        },
        {
            "target": "execute_qft_gr_conservation_form_scope_assumption_reduction_attempt",
            "decision": "deferred",
            "reason": "Execution requires this packet's result review first.",
        },
        {
            "target": "prepare_qft_gr_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "reason": "Selecting a conservation form does not authorize source admissibility.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": "This packet does not authorize a conservation proof-object attempt.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized by preparation.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "No operator-domain row packet closes QFT-GR.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is outside this bounded packet.",
        },
    ]


def build_qft_gr_conservation_form_scope_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    operator_domain_packet_path: Path = DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    operator_domain_packet = _read_json(operator_domain_packet_path)
    rows = operator_domain_packet.get("operator_domain_assumption_rows", [])
    selected_row = _row_by_id(rows, SELECTED_ROW_ID)
    conservation_form_options = _conservation_form_options()
    candidate_next_targets = _candidate_next_targets()

    selected_row_payload: dict[str, Any] = {}
    if selected_row:
        selected_row_payload = {
            "assumption_id": selected_row["assumption_id"],
            "assumption_family": selected_row["assumption_family"],
            "current_status": selected_row["current_status"],
            "conservation_form_options": CONSERVATION_FORM_OPTIONS,
            "conservation_form_option_decisions": conservation_form_options,
            "selected_bounded_conservation_form": SELECTED_BOUNDED_CONSERVATION_FORM,
            "available_repo_evidence": selected_row["available_repo_evidence"],
            "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
            "source_row_required_future_proof_object": selected_row[
                "required_future_proof_object"
            ],
            "candidate_reduction_route": selected_row["reduction_route"],
            "claim_ceiling": (
                "conservation_form_scope_packet_only_no_conservation_proof_"
                "object_no_conservation_witness_no_source_admissibility"
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
        "result_review_accepts_prior_row_only": result_review.get("accepted") is True
        and result_review.get("review_decision") == "accepted"
        and result_review.get("completed_operator_domain_row") == PRIOR_ACCEPTED_ROW004,
        "prior_renormalized_expectation_domain_link_contract_accepted": result_review.get(
            "accepted_contract_id"
        )
        == RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
        "prior_rows001_002_003_preserved": result_review.get(
            "prior_accepted_operator_domain_assumption_rows"
        )
        == [PRIOR_ACCEPTED_ROW001, PRIOR_ACCEPTED_ROW002, PRIOR_ACCEPTED_ROW003],
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
        "selects_only_conservation_form_scope_row": selected_row is not None
        and result_review.get("next_operator_domain_assumption_row")
        == SELECTED_ROW_ID,
        "selected_row_status_tokens_current": selected_status
        == ["required", "missing", "candidate_reducible"],
        "selected_row_status_values_valid": all(
            status in ROW_STATUS_ENUM for status in selected_status
        ),
        "conservation_form_options_complete": CONSERVATION_FORM_OPTIONS
        == ["weak", "strong", "distributional"],
        "bounded_conservation_form_selected": selected_row_payload.get(
            "selected_bounded_conservation_form"
        )
        == SELECTED_BOUNDED_CONSERVATION_FORM
        and conservation_form_options[0]["decision"] == "selected",
        "required_future_proof_object_recorded": selected_row_payload.get(
            "required_future_proof_object"
        )
        == REQUIRED_FUTURE_PROOF_OBJECT,
        "prepares_reduction_analysis_only": bool(selected_row_payload),
        "does_not_prove_conservation": result_review.get(
            "renormalization_compatibility_with_conservation_claimed"
        )
        is False,
        "does_not_claim_source_admissibility": result_review.get(
            "source_admissibility_claimed"
        )
        is False
        and result_review.get("stress_energy_source_admissibility_claimed") is False,
        "does_not_construct_conservation_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed") is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_bianchi_compatibility": result_review.get(
            "Bianchi_compatibility_claimed"
        )
        is False,
        "does_not_derive_semiclassical_einstein_equation": result_review.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "does_not_close_qft_gr_seam": result_review.get("qft_gr_seam_closed")
        is False,
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
        else "QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "prior_accepted_operator_domain_assumption_rows": [
            PRIOR_ACCEPTED_ROW001,
            PRIOR_ACCEPTED_ROW002,
            PRIOR_ACCEPTED_ROW003,
            PRIOR_ACCEPTED_ROW004,
        ],
        "prior_accepted_selected_operator_action_contract": SELECTED_OPERATOR_ACTION_CONTRACT_ID,
        "prior_accepted_candidate_source_domain_membership_contract": CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_CONTRACT_ID,
        "prior_accepted_state_expectation_domain_link_contract": STATE_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
        "prior_accepted_renormalized_expectation_domain_link_contract": RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
        "source_operator_domain_assumption_reduction_packet": EXPECTED_OPERATOR_DOMAIN_PACKET_ID,
        "source_operator_domain_assumption_reduction_packet_pointer": _ptr(
            operator_domain_packet_path
        ),
        "blocker": "insufficient_assumptions_for_conservation",
        "selected_blocker": "insufficient_assumptions_for_conservation",
        "current_family": PRIMARY_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_operator_domain_assumption_row": SELECTED_ROW_ID,
        "conservation_form_scope_assumption_reduction_analysis_prepared": prepared,
        "conservation_form_scope_assumption": selected_row_payload,
        "conservation_form_options": CONSERVATION_FORM_OPTIONS,
        "conservation_form_option_decisions": conservation_form_options,
        "selected_bounded_conservation_form": SELECTED_BOUNDED_CONSERVATION_FORM,
        "required_future_proof_object": REQUIRED_FUTURE_PROOF_OBJECT,
        "conservation_form_scope_status_tokens": selected_status,
        "row_status_enum": ROW_STATUS_ENUM,
        "selected_row_count": 1 if selected_row_payload else 0,
        "claim_ceiling": (
            "conservation_form_scope_assumption_reduction_packet_only_no_"
            "conservation_proof_object_no_conservation_witness_no_source_"
            "admissibility_no_qft_gr_seam_closure"
        ),
        "conservation_form_scope_assumption_discharged": False,
        "conservation_form_scope_claimed_as_conservation_proof": False,
        "conservation_form_selected_as_source_admissibility": False,
        "conservation_proved": False,
        "covariant_conservation_statement_proved": False,
        "actual_conservation_claimed": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "assumptions_reduced_or_discharged_by_preparation": False,
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
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_conservation_form_scope_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_conservation_form_scope_assumption_reduction_packet_result_"
            "review_after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_CONSERVATION_FORM_SCOPE_ASSUMPTION_REDUCTION_PACKET_"
            "RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only OD-ASSUMP-005 conservation-form-scope "
            "reduction analysis and selects the bounded weak operator-domain "
            "conservation form for future proof-object work. It does not prove "
            "conservation, construct a conservation proof object or conservation "
            "witness, claim source admissibility or Bianchi compatibility, derive "
            "the semiclassical Einstein equation, close QFT-GR, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_conservation_form_scope_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    operator_domain_packet_path: Path = DEFAULT_OPERATOR_DOMAIN_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_conservation_form_scope_assumption_reduction_packet(
        result_review_path=result_review_path,
        operator_domain_packet_path=operator_domain_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR conservation-form-scope assumption-reduction packet."
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
    payload = write_qft_gr_conservation_form_scope_assumption_reduction_packet(
        result_review_path=result_review_path,
        operator_domain_packet_path=operator_domain_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_conservation_form_scope_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} row={payload['selected_operator_domain_assumption_row']} "
        f"form={payload['selected_bounded_conservation_form']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
