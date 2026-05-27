from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_assumption_reduction_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PRIMARY_BLOCKER,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-05-26T00:00:00Z"
SCHEMA_ID = "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260526_v0"
PACKET_ID = "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_operator_domain_assumption_reduction_packet_prepared_no_"
    "conservation_witness_or_seam_closure"
)
PRIMARY_ASSUMPTION_FAMILY = "operator_domain_assumptions"
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "review_qft_gr_operator_domain_assumption_reduction_packet_result"
ROW_STATUS_ENUM = [
    "required",
    "supplied",
    "derivable",
    "missing",
    "candidate_reducible",
    "not_reducible_in_current_lane",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260526_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _operator_domain_assumption_rows() -> list[dict[str, Any]]:
    claim_ceiling = "operator_domain_assumption_reduction_only_no_conservation_witness"
    return [
        {
            "assumption_id": "OD-ASSUMP-001-selected_operator_action",
            "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "supplied",
                "missing",
                "candidate_reducible",
            ],
            "available_repo_evidence": [
                "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_v0",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "operator_action_selected_and_typed_for_candidate_source_conservation_statement"
            ),
            "reduction_route": (
                "reuse prepared covariant derivative/operator-domain structure, then "
                "pin the exact operator action needed by the conservation proof-object route"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the later conservation proof object can still change operator semantics or "
                "become ill-typed"
            ),
        },
        {
            "assumption_id": "OD-ASSUMP-002-candidate_source_domain_membership",
            "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "missing",
                "candidate_reducible",
            ],
            "available_repo_evidence": [
                "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_v0",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
            ],
            "required_future_proof_object": (
                "candidate_stress_energy_source_in_prepared_operator_domain"
            ),
            "reduction_route": (
                "separate source-domain membership from source admissibility and prove only "
                "the bounded operator-domain membership precondition"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the covariant divergence may not be applicable to the candidate source"
            ),
        },
        {
            "assumption_id": "OD-ASSUMP-003-state_expectation_domain_link",
            "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "missing",
                "candidate_reducible",
            ],
            "available_repo_evidence": [
                "QFT_GR_StateExpectationFunctionalSemantics",
                "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_PACKET_v0",
            ],
            "required_future_proof_object": (
                "state_expectation_semantics_preserve_operator_domain_membership"
            ),
            "reduction_route": (
                "bind state-expectation semantics to the prepared operator domain without "
                "claiming conservation or source admissibility"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "state expectations may be meaningful while still outside the selected "
                "operator domain"
            ),
        },
        {
            "assumption_id": "OD-ASSUMP-004-renormalized_expectation_domain_link",
            "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "missing",
                "candidate_reducible",
            ],
            "available_repo_evidence": [
                "QFT_GR_RenormalizedExpectationValueSemantics",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
            ],
            "required_future_proof_object": (
                "renormalized_expectation_value_admitted_to_operator_domain"
            ),
            "reduction_route": (
                "reduce the domain-link obligation for renormalized expectation values "
                "while leaving renormalization compatibility with conservation downstream"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "renormalized expectation semantics can remain supplied-only relative to "
                "the conservation operator"
            ),
        },
        {
            "assumption_id": "OD-ASSUMP-005-conservation_form_scope",
            "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "missing",
                "candidate_reducible",
            ],
            "available_repo_evidence": [
                "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_v0",
                "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_v0",
            ],
            "required_future_proof_object": (
                "bounded_conservation_form_scope_selected_for_future_proof_object"
            ),
            "reduction_route": (
                "fix whether the future statement uses strong, weak, or distributional "
                "operator-domain conservation before any witness attempt"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the conservation proof object remains ambiguous between incompatible "
                "statement forms"
            ),
        },
        {
            "assumption_id": "OD-ASSUMP-006-metric_connection_scope",
            "assumption_family": PRIMARY_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "supplied",
                "missing",
                "candidate_reducible",
            ],
            "available_repo_evidence": [
                "QFT_GR_COVARIANT_DERIVATIVE_OPERATOR_DOMAIN_PACKET_v0",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "bounded_metric_connection_scope_supports_selected_operator_domain"
            ),
            "reduction_route": (
                "extract the bounded metric/connection assumptions required for the "
                "selected operator without claiming Bianchi compatibility"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "operator-domain membership remains tied to underspecified background "
                "geometry"
            ),
        },
    ]


def _not_reducible_in_current_lane() -> list[dict[str, str]]:
    return [
        {
            "assumption_id": "OD-NONRED-001-conservation-proof-object",
            "reason": "A future proof object is downstream of this reduction packet.",
        },
        {
            "assumption_id": "OD-NONRED-002-source-admissibility",
            "reason": "Source admissibility requires conservation and Bianchi dependencies.",
        },
        {
            "assumption_id": "OD-NONRED-003-bianchi-compatibility",
            "reason": "Bianchi compatibility is a separate downstream geometric obligation.",
        },
        {
            "assumption_id": "OD-NONRED-004-renormalization-conservation-theorem",
            "reason": "Renormalization compatibility with conservation remains a separate family.",
        },
        {
            "assumption_id": "OD-NONRED-005-qft-gr-seam-closure",
            "reason": "Operator-domain assumption reduction cannot close QFT-GR.",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The prepared operator-domain assumption-reduction packet must be reviewed before any further reduction route is selected.",
        },
        {
            "target": "prepare_qft_gr_state_domain_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "State-domain reduction remains downstream of this packet review.",
        },
        {
            "target": "prepare_qft_gr_renormalization_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Renormalization reduction remains a separate assumption family.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "not_authorized",
            "reason": "A proof-object attempt remains blocked until assumption reduction is reviewed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Operator-domain assumption reduction does not close QFT-GR.",
        },
    ]


def build_qft_gr_operator_domain_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    rows = _operator_domain_assumption_rows()
    not_reducible = _not_reducible_in_current_lane()
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
        == PRIMARY_BLOCKER,
        "selects_operator_domain_assumption_family": result_review.get(
            "primary_assumption_reduction_family"
        )
        == PRIMARY_ASSUMPTION_FAMILY,
        "operator_domain_rows_complete": len(rows) == 6
        and all(required_row_fields <= set(row) for row in rows),
        "row_status_enum_pinned": all(
            status in ROW_STATUS_ENUM
            for row in rows
            for status in row["current_status"]
        ),
        "all_rows_current_family": all(
            row["assumption_family"] == PRIMARY_ASSUMPTION_FAMILY for row in rows
        ),
        "prepares_reduction_analysis_only": True,
        "does_not_discharge_assumptions": True,
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
        else "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_assumption_reduction_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_covariant_conservation_assumption_reduction_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "blocker": PRIMARY_BLOCKER,
        "selected_blocker": PRIMARY_BLOCKER,
        "primary_assumption_reduction_family": PRIMARY_ASSUMPTION_FAMILY,
        "selected_assumption_family": PRIMARY_ASSUMPTION_FAMILY,
        "row_status_enum": ROW_STATUS_ENUM,
        "operator_domain_assumption_inventory_prepared": prepared,
        "operator_domain_assumption_reduction_analysis_prepared": prepared,
        "operator_domain_assumption_rows": rows,
        "operator_domain_assumption_row_count": len(rows),
        "required_vs_supplied_operator_assumptions": [
            row["assumption_id"] for row in rows if "supplied" in row["current_status"]
        ],
        "candidate_reducible_operator_assumptions": [
            row["assumption_id"]
            for row in rows
            if "candidate_reducible" in row["current_status"]
        ],
        "not_reducible_in_current_lane_operator_assumptions": not_reducible,
        "required_future_proof_objects": [
            row["required_future_proof_object"] for row in rows
        ],
        "claim_ceiling": "operator_domain_assumption_reduction_packet_only",
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
        else "REMEDIATE_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_operator_domain_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_operator_domain_assumption_reduction_packet_result_review_after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_ONLY_"
            "NO_ASSUMPTION_DISCHARGE_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares operator-domain assumption-reduction analysis "
            "only. It does not discharge assumptions, construct a conservation "
            "proof object or conservation witness, claim source admissibility "
            "or Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, promote the master "
            "action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_operator_domain_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_operator_domain_assumption_reduction_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR operator-domain assumption-reduction packet."
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
    payload = write_qft_gr_operator_domain_assumption_reduction_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_operator_domain_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} rows={payload['operator_domain_assumption_row_count']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
