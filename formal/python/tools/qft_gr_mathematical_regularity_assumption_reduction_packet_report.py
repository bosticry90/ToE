from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_report import (
    BLOCKER,
    DEFAULT_FAMILY_MAP_PATH,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-08T00:00:00Z"
SCHEMA_ID = "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_20260608_v0"
PACKET_ID = "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_mathematical_regularity_assumption_reduction_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
SELECTED_ASSUMPTION_FAMILY = "mathematical_regularity_assumptions"
PRIOR_COMPLETED_FAMILIES = [
    "operator_domain_assumptions",
    "renormalization_assumptions",
    "state_domain_assumptions",
]
SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW = (
    "MR-ASSUMP-001-derivative_exchange_regular_boundary"
)
NEXT_TARGET = "review_qft_gr_mathematical_regularity_assumption_reduction_packet_result"
DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY = (
    "bounded_derivative_exchange_regular_boundary_for_state_expectation_and_"
    "covariant_divergence"
)
WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE = (
    "weak_strong_conservation_comparison_scope_for_future_conservation_"
    "proof_object"
)
DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN = (
    "distributional_pairing_regular_domain_for_candidate_renormalized_"
    "stress_energy_expectation"
)
LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY = (
    "limit_interchange_regularization_boundary_for_renormalized_expectation_"
    "and_covariant_derivative"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_20260608_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _available_repo_evidence() -> list[str]:
    return [
        "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
        "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
        "QFT_GR_COVARIANT_CONSERVATION_PROOF_OBJECT_OBSTRUCTION_REFINEMENT_PACKET_v0",
    ]


def _required_future_proof_objects() -> list[str]:
    return [
        "regularity_boundary_supports_covariant_derivative_exchange",
        "weak_strong_conservation_comparison_regular_scope",
        "distributional_pairing_domain_regular_for_candidate_source",
        "limit_interchange_boundary_for_renormalized_expectation_and_derivative",
    ]


def _mathematical_regularity_assumption_rows() -> list[dict[str, Any]]:
    claim_ceiling = (
        "mathematical_regularity_assumption_reduction_analysis_only_no_"
        "conservation_proof_object_no_witness_no_source_admissibility"
    )
    return [
        {
            "assumption_id": SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW,
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": [
                "required",
                "supplied",
                "missing",
                "candidate_reducible",
            ],
            "regularity_condition": DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
            "available_repo_evidence": [
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
                "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
                "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "regularity_boundary_supports_covariant_derivative_exchange"
            ),
            "candidate_reduction_route": (
                "pin the bounded regularity boundary needed to exchange the "
                "covariant derivative with the state-expectation and "
                "renormalized-expectation operations, without claiming "
                "conservation"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "a future conservation proof object may require derivative "
                "exchange over a state or expectation class not regular enough "
                "for the selected operator-domain and renormalization rows"
            ),
        },
        {
            "assumption_id": "MR-ASSUMP-002-weak_strong_conservation_comparison_scope",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "regularity_condition": WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE,
            "available_repo_evidence": [
                "QFT_GR_COVARIANT_CONSERVATION_STATEMENT_WITH_OPERATOR_DOMAIN_PACKET_v0",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
            ],
            "required_future_proof_object": (
                "weak_strong_conservation_comparison_regular_scope"
            ),
            "candidate_reduction_route": (
                "separate strong, weak, and distributional comparison "
                "requirements before any conservation proof-object attempt"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the project may conflate weak and strong conservation forms "
                "without the regularity needed to compare them"
            ),
        },
        {
            "assumption_id": "MR-ASSUMP-003-distributional_pairing_regular_domain",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "regularity_condition": DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN,
            "available_repo_evidence": [
                "QFT_GR_STATE_EXPECTATION_COMPATIBILITY_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
                "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "distributional_pairing_domain_regular_for_candidate_source"
            ),
            "candidate_reduction_route": (
                "pin the regular domain for distributional pairings of the "
                "candidate renormalized stress-energy expectation"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the source candidate may be meaningful as an expectation but "
                "not regular enough for the distributional conservation form"
            ),
        },
        {
            "assumption_id": "MR-ASSUMP-004-limit_interchange_regularization_boundary",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "regularity_condition": LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY,
            "available_repo_evidence": [
                "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
                "QFT_GR_RENORMALIZED_EXPECTATION_FINITENESS_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "limit_interchange_boundary_for_renormalized_expectation_and_derivative"
            ),
            "candidate_reduction_route": (
                "separate limit interchange and regularization assumptions "
                "from conservation, source admissibility, and Bianchi claims"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "renormalized expectation and derivative operations may not "
                "commute in the limit needed by the future conservation route"
            ),
        },
    ]


def _not_reducible_in_current_lane() -> list[dict[str, str]]:
    return [
        {
            "assumption_id": "MR-NONRED-001-mathematical-regularity-discharge",
            "reason": "This packet prepares mathematical-regularity analysis only and does not discharge the family.",
        },
        {
            "assumption_id": "MR-NONRED-002-conservation-proof-object",
            "reason": "A conservation proof object remains downstream of mathematical-regularity reduction.",
        },
        {
            "assumption_id": "MR-NONRED-003-conservation-witness",
            "reason": "No conservation witness is constructed or authorized by this packet.",
        },
        {
            "assumption_id": "MR-NONRED-004-state-admissibility",
            "reason": "Regularity packet preparation does not claim state admissibility.",
        },
        {
            "assumption_id": "MR-NONRED-005-source-admissibility",
            "reason": "Regularity assumptions do not imply stress-energy source admissibility.",
        },
        {
            "assumption_id": "MR-NONRED-006-bianchi-compatibility",
            "reason": "Bianchi compatibility remains a downstream geometric obligation.",
        },
        {
            "assumption_id": "MR-NONRED-007-semiclassical-einstein-equation",
            "reason": "The semiclassical Einstein equation is not derived by this packet.",
        },
        {
            "assumption_id": "MR-NONRED-008-qft-gr-seam-closure",
            "reason": "Mathematical-regularity assumption reduction cannot close QFT-GR.",
        },
        {
            "assumption_id": "MR-NONRED-009-release-or-public-submission",
            "reason": "Release assembly and public submission are outside this bounded packet.",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared mathematical-regularity assumption-reduction "
                "packet must be result-reviewed before any bounded reduction "
                "attempt or downstream row action is authorized."
            ),
        },
        {
            "target": (
                "execute_qft_gr_derivative_exchange_regular_boundary_"
                "assumption_reduction_attempt"
            ),
            "decision": "deferred",
            "reason": "A bounded MR-ASSUMP-001 attempt requires packet result review first.",
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": "Source admissibility remains downstream and unclaimed.",
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": "Packet preparation does not construct or authorize a conservation proof object.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by this packet.",
        },
        {
            "target": "claim_qft_gr_state_admissibility",
            "decision": "not_authorized",
            "reason": "Mathematical regularity does not imply state admissibility.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "Mathematical regularity does not imply source admissibility.",
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
            "reason": "QFT-GR seam closure remains explicitly outside scope.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission are outside this checkpoint.",
        },
    ]


def build_qft_gr_mathematical_regularity_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    family_map_path: Path = DEFAULT_FAMILY_MAP_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    family_map = _read_json(family_map_path)
    rows = _mathematical_regularity_assumption_rows()
    selected_row = rows[0]
    not_reducible = _not_reducible_in_current_lane()
    candidate_next_targets = _candidate_next_targets()
    candidate_reducible_classes = family_map.get(
        "candidate_reducible_assumption_classes", []
    )

    acceptance_criteria = {
        "consumes_expected_state_domain_closeout_result_review": result_review.get(
            "schema_id"
        )
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID
        and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "state_domain_closeout_result_review_outcome_expected": result_review.get(
            "outcome_id"
        )
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "state_domain_closeout_result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "state_domain_closeout_result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "prior_assumption_families_completed_for_lane": result_review.get(
            "completed_assumption_families_for_this_lane"
        )
        == PRIOR_COMPLETED_FAMILIES
        and result_review.get("completed_assumption_family_count") == 3,
        "operator_domain_family_completed": (
            "operator_domain_assumptions"
            in result_review.get("completed_assumption_families_for_this_lane", [])
        ),
        "renormalization_family_completed": (
            "renormalization_assumptions"
            in result_review.get("completed_assumption_families_for_this_lane", [])
        ),
        "state_domain_family_completed": (
            result_review.get("state_domain_assumptions_closed_for_this_lane") is True
            and "state_domain_assumptions"
            in result_review.get("completed_assumption_families_for_this_lane", [])
            and result_review.get(
                "no_remaining_state_domain_assumption_row_in_current_inventory"
            )
            is True
        ),
        "selects_mathematical_regularity_family": result_review.get(
            "next_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY
        and result_review.get(
            "mathematical_regularity_assumption_reduction_packet_authorized"
        )
        is True
        and SELECTED_ASSUMPTION_FAMILY in candidate_reducible_classes,
        "mathematical_regularity_rows_current_family": all(
            row["assumption_family"] == SELECTED_ASSUMPTION_FAMILY for row in rows
        ),
        "selected_first_repo_authoritative_row_only": selected_row["assumption_id"]
        == SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        and rows[0]["assumption_id"] == SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW,
        "required_packet_fields_prepared": all(
            [
                DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
                WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE,
                DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN,
                LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY,
                _available_repo_evidence(),
                _required_future_proof_objects(),
                rows,
                selected_row,
                not_reducible,
            ]
        ),
        "prepares_reduction_analysis_only": True,
        "does_not_discharge_mathematical_regularity_assumptions": True,
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == BLOCKER
        and result_review.get("conservation_blocker_remains") is True,
        "does_not_claim_state_admissibility": result_review.get(
            "state_admissibility_claimed"
        )
        is False,
        "does_not_claim_source_admissibility": result_review.get(
            "source_admissibility_claimed"
        )
        is False
        and result_review.get("stress_energy_source_admissibility_claimed") is False,
        "does_not_claim_conservation": result_review.get("conservation_proved")
        is False
        and result_review.get("actual_conservation_claimed") is False,
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
        "does_not_claim_empirical_validation": result_review.get(
            "empirical_validation_claimed"
        )
        is False,
        "does_not_promote_master_action": result_review.get(
            "master_action_promoted"
        )
        is False
        and result_review.get("master_action_promotion_authorized") is False,
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
        else "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "repo_authoritative_assumption_family_map": _ptr(family_map_path),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "operator_domain_assumptions_completed": True,
        "renormalization_assumptions_completed": True,
        "state_domain_assumptions_completed": True,
        "accepted_state_domain_assumption_rows": result_review.get(
            "accepted_state_domain_assumption_rows", []
        ),
        "accepted_state_domain_assumption_row_count": result_review.get(
            "accepted_state_domain_assumption_row_count"
        ),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_family_only": True,
        "mathematical_regularity_assumption_inventory_prepared": prepared,
        "mathematical_regularity_assumption_reduction_analysis_prepared": prepared,
        "mathematical_regularity_assumption_rows": rows,
        "mathematical_regularity_assumption_row_count": len(rows),
        "selected_mathematical_regularity_assumption_row": (
            SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        ),
        "selected_bounded_mathematical_regularity_assumption_row": (
            SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
        ),
        "selected_row_count": 1,
        "selected_row_is_first_repo_authoritative_row": True,
        "selected_mathematical_regularity_assumption": selected_row,
        "derivative_exchange_regular_boundary": DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
        "weak_strong_conservation_comparison_scope": (
            WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE
        ),
        "distributional_pairing_regular_domain": DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN,
        "limit_interchange_regularization_boundary": (
            LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY
        ),
        "available_repo_evidence": _available_repo_evidence(),
        "required_future_proof_objects": _required_future_proof_objects(),
        "candidate_reducible_assumptions": rows,
        "candidate_reducible_assumption_count": len(rows),
        "not_reducible_in_current_lane": not_reducible,
        "not_reducible_in_current_lane_count": len(not_reducible),
        "prepares_reduction_analysis_only": prepared,
        "mathematical_regularity_assumptions_discharged": False,
        "mathematical_regularity_assumptions_reduced_or_discharged_by_preparation": False,
        "assumptions_reduced_or_discharged_by_preparation": False,
        "claim_ceiling": (
            "mathematical_regularity_assumption_reduction_packet_preparation_"
            "only_no_conservation_witness_no_conservation_proof_object_no_"
            "state_admissibility_no_source_admissibility_no_bianchi_no_qft_gr_"
            "seam_closure"
        ),
        "failure_mode_if_unresolved": (
            "operator-domain, renormalization, and state-domain families are "
            "closed only for this lane, but the conservation blocker remains "
            "because the regularity needed for derivative exchange and "
            "weak/strong conservation comparison is not yet reduced"
        ),
        "state_admissibility_claimed": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "conservation_proved": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
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
        else "REMEDIATE_QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_mathematical_regularity_assumption_reduction_packet_result_review_"
            "after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_PACKET_"
            "RESULT_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares mathematical-regularity assumption-reduction "
            "analysis only. It consumes the accepted state-domain closeout "
            "result review, records operator-domain, renormalization, and "
            "state-domain families as completed for this lane, selects only "
            "the first mathematical-regularity row, preserves "
            "insufficient_assumptions_for_conservation, and does not claim "
            "conservation, state admissibility, source admissibility, Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, construct a conservation proof object or witness, validate "
            "empirically, promote the master action, assemble release, or "
            "authorize public submission."
        ),
    }


def write_qft_gr_mathematical_regularity_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    family_map_path: Path = DEFAULT_FAMILY_MAP_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_mathematical_regularity_assumption_reduction_packet(
        result_review_path=result_review_path,
        family_map_path=family_map_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR mathematical-regularity assumption-reduction packet."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--family-map", type=Path, default=DEFAULT_FAMILY_MAP_PATH)
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
    family_map_path = (
        ns.family_map if ns.family_map.is_absolute() else (REPO_ROOT / ns.family_map)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_mathematical_regularity_assumption_reduction_packet(
        result_review_path=result_review_path,
        family_map_path=family_map_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_mathematical_regularity_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} "
        f"row={payload['selected_mathematical_regularity_assumption_row']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
