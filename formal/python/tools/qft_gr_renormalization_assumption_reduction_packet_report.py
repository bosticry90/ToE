from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_ASSUMPTION_FAMILY as EXPECTED_NEXT_ASSUMPTION_FAMILY,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-06T00:00:00Z"
SCHEMA_ID = "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_20260606_v0"
PACKET_ID = "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_renormalization_assumption_reduction_packet_prepared_with_no_"
    "conservation_witness_or_seam_closure"
)
BLOCKER = "insufficient_assumptions_for_conservation"
PRIOR_COMPLETED_FAMILY = "operator_domain_assumptions"
SELECTED_ASSUMPTION_FAMILY = "renormalization_assumptions"
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "review_qft_gr_renormalization_assumption_reduction_packet_result"
RENORMALIZED_STRESS_ENERGY_OBJECT = (
    "candidate_renormalized_qft_stress_energy_expectation_object"
)
RENORMALIZATION_SCOPE = (
    "bounded_repo_local_renormalization_scope_for_candidate_stress_energy_"
    "expectation"
)
RENORMALIZED_EXPECTATION_DOMAIN = (
    "renormalized_expectation_value_admitted_to_selected_operator_domain"
)
FINITENESS_REGULARITY_BOUNDARY = (
    "finite_regular_renormalized_expectation_required_before_conservation_"
    "proof_object"
)
OPERATOR_DOMAIN_COMPATIBILITY = (
    "compatible_with_reduced_operator_domain_rows_OD_ASSUMP_001_through_006_"
    "without_conservation_claim"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_20260606_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _available_repo_evidence() -> list[str]:
    return [
        "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_RESULT_REVIEW_v0",
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
        "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_v0",
        "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
    ]


def _required_future_proof_objects() -> list[str]:
    return [
        "renormalization_prescription_defines_finite_candidate_stress_energy_expectation",
        "renormalized_expectation_regular_in_selected_operator_domain",
        "renormalization_scope_compatible_with_selected_operator_domain_structure",
        "renormalized_expectation_covariant_divergence_compatibility_for_future_conservation_proof_object",
    ]


def _candidate_reducible_assumptions() -> list[dict[str, Any]]:
    claim_ceiling = (
        "renormalization_assumption_reduction_analysis_only_no_conservation_"
        "proof_object_no_witness"
    )
    return [
        {
            "assumption_id": "RN-ASSUMP-001-renormalized_stress_energy_object",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "supplied", "candidate_reducible"],
            "available_repo_evidence": [
                "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_RESULT_REVIEW_v0",
                "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_v0",
            ],
            "required_future_proof_object": (
                "renormalized_stress_energy_object_selected_for_candidate_source"
            ),
            "candidate_reduction_route": (
                "pin the candidate renormalized stress-energy expectation object "
                "without claiming it is conserved or source-admissible"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "later conservation work can still change which renormalized "
                "stress-energy object is under test"
            ),
        },
        {
            "assumption_id": "RN-ASSUMP-002-renormalization_scope",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "available_repo_evidence": [
                "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_RESULT_REVIEW_v0",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
            ],
            "required_future_proof_object": (
                "bounded_renormalization_scope_defined_for_candidate_source"
            ),
            "candidate_reduction_route": (
                "separate the bounded repo-local renormalization scope from "
                "scheme-independence, source admissibility, and conservation"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "renormalized expectation claims remain scope-ambiguous before "
                "the conservation proof-object route"
            ),
        },
        {
            "assumption_id": "RN-ASSUMP-003-renormalized_expectation_domain",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "available_repo_evidence": [
                "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
                "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "renormalized_expectation_value_admitted_to_selected_operator_domain"
            ),
            "candidate_reduction_route": (
                "reuse the accepted operator-domain structure to pin the "
                "renormalized expectation domain without asserting conservation"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the renormalized source may remain meaningful only outside the "
                "selected conservation operator domain"
            ),
        },
        {
            "assumption_id": "RN-ASSUMP-004-finiteness_regular_boundary",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "available_repo_evidence": [
                "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_v0",
                "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0",
            ],
            "required_future_proof_object": (
                "finite_regular_renormalized_expectation_boundary_for_future_conservation_statement"
            ),
            "candidate_reduction_route": (
                "bound the finiteness and regularity preconditions needed before "
                "testing covariant-divergence compatibility"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the conservation blocker remains mixed with finiteness or "
                "regularity failures"
            ),
        },
        {
            "assumption_id": "RN-ASSUMP-005-operator_domain_compatibility",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "available_repo_evidence": [
                "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
                "QFT_GR_METRIC_CONNECTION_SCOPE_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "renormalization_scope_compatible_with_selected_operator_domain_structure"
            ),
            "candidate_reduction_route": (
                "check compatibility with the selected operator-domain structure "
                "while preserving no Bianchi, conservation, or source-admissibility claim"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "operator-domain assumptions are reduced for this lane, but the "
                "renormalized object may not fit the selected structure"
            ),
        },
    ]


def _not_reducible_in_current_lane() -> list[dict[str, str]]:
    return [
        {
            "assumption_id": "RN-NONRED-001-renormalization-assumption-discharge",
            "reason": "This packet prepares analysis only and does not discharge the renormalization family.",
        },
        {
            "assumption_id": "RN-NONRED-002-conservation-proof-object",
            "reason": "A conservation proof object remains downstream of assumption reduction.",
        },
        {
            "assumption_id": "RN-NONRED-003-conservation-witness",
            "reason": "No conservation witness is constructed or authorized by this packet.",
        },
        {
            "assumption_id": "RN-NONRED-004-source-admissibility",
            "reason": "Source admissibility requires conservation and Bianchi dependencies.",
        },
        {
            "assumption_id": "RN-NONRED-005-bianchi-compatibility",
            "reason": "Bianchi compatibility is a separate downstream geometric obligation.",
        },
        {
            "assumption_id": "RN-NONRED-006-semiclassical-einstein-equation",
            "reason": "The semiclassical Einstein equation is not derived by renormalization packet preparation.",
        },
        {
            "assumption_id": "RN-NONRED-007-qft-gr-seam-closure",
            "reason": "Renormalization assumption reduction cannot close the QFT-GR seam.",
        },
        {
            "assumption_id": "RN-NONRED-008-release-or-public-submission",
            "reason": "Release assembly and public submission are outside this scientific packet.",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared renormalization assumption-reduction packet must "
                "be result-reviewed before any reduction attempt or downstream "
                "conservation route is authorized."
            ),
        },
        {
            "target": "execute_qft_gr_renormalization_assumption_reduction_attempt",
            "decision": "deferred",
            "reason": "A bounded reduction attempt requires packet result review first.",
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
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "Renormalization assumptions alone do not imply source admissibility.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains explicitly outside scope.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is outside this bounded checkpoint.",
        },
    ]


def build_qft_gr_renormalization_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    candidate_reducible = _candidate_reducible_assumptions()
    not_reducible = _not_reducible_in_current_lane()
    candidate_next_targets = _candidate_next_targets()

    acceptance_criteria = {
        "consumes_expected_operator_domain_closeout_result_review": result_review.get(
            "schema_id"
        )
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID
        and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID,
        "closeout_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "closeout_result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "closeout_result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == BLOCKER
        and result_review.get("conservation_blocker_remains") is True,
        "prior_operator_domain_family_completed_for_lane": result_review.get(
            "operator_domain_assumptions_closed_for_this_lane"
        )
        is True
        and result_review.get("accepted_operator_domain_assumption_row_count") == 6,
        "selects_only_renormalization_assumptions": EXPECTED_NEXT_ASSUMPTION_FAMILY
        == SELECTED_ASSUMPTION_FAMILY
        and result_review.get("next_assumption_family") == SELECTED_ASSUMPTION_FAMILY,
        "required_packet_fields_prepared": all(
            [
                RENORMALIZED_STRESS_ENERGY_OBJECT,
                RENORMALIZATION_SCOPE,
                RENORMALIZED_EXPECTATION_DOMAIN,
                FINITENESS_REGULARITY_BOUNDARY,
                OPERATOR_DOMAIN_COMPATIBILITY,
                _available_repo_evidence(),
                _required_future_proof_objects(),
                candidate_reducible,
                not_reducible,
            ]
        ),
        "candidate_reducible_rows_current_family": all(
            row["assumption_family"] == SELECTED_ASSUMPTION_FAMILY
            for row in candidate_reducible
        ),
        "prepares_reduction_analysis_only": True,
        "does_not_discharge_renormalization_assumptions": True,
        "does_not_construct_conservation_proof_object": result_review.get(
            "conservation_proof_object_constructed"
        )
        is False
        and result_review.get("proof_object_constructed") is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_source_admissibility": result_review.get(
            "stress_energy_source_admissibility_claimed"
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
        else "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_pointer": _ptr(
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
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_family_only": True,
        "prior_completed_family": PRIOR_COMPLETED_FAMILY,
        "prior_completed_family_scope": (
            "operator_domain_assumptions_closed_only_for_this_assumption_reduction_lane"
        ),
        "prior_completed_operator_domain_assumption_rows": result_review.get(
            "accepted_operator_domain_assumption_rows", []
        ),
        "prior_completed_operator_domain_assumption_row_count": result_review.get(
            "accepted_operator_domain_assumption_row_count"
        ),
        "renormalized_stress_energy_object": RENORMALIZED_STRESS_ENERGY_OBJECT,
        "renormalization_scope": RENORMALIZATION_SCOPE,
        "renormalized_expectation_domain": RENORMALIZED_EXPECTATION_DOMAIN,
        "finiteness_regular_boundary": FINITENESS_REGULARITY_BOUNDARY,
        "compatibility_with_selected_operator_domain_structure": (
            OPERATOR_DOMAIN_COMPATIBILITY
        ),
        "available_repo_evidence": _available_repo_evidence(),
        "required_future_proof_objects": _required_future_proof_objects(),
        "candidate_reducible_assumptions": candidate_reducible,
        "candidate_reducible_assumption_count": len(candidate_reducible),
        "not_reducible_in_current_lane": not_reducible,
        "not_reducible_in_current_lane_count": len(not_reducible),
        "renormalization_assumption_reduction_analysis_prepared": prepared,
        "prepares_reduction_analysis_only": prepared,
        "renormalization_assumptions_discharged": False,
        "renormalization_assumptions_reduced_or_discharged_by_preparation": False,
        "claim_ceiling": (
            "renormalization_assumption_reduction_packet_preparation_only_no_"
            "conservation_witness_no_conservation_proof_object_no_source_"
            "admissibility_no_bianchi_no_qft_gr_seam_closure"
        ),
        "failure_mode_if_unresolved": (
            "operator-domain assumptions are closed only for this lane, but "
            "the conservation blocker remains because the renormalized stress-"
            "energy object, scope, domain, finiteness or regularity boundary, "
            "and selected operator-domain compatibility are not yet result-reviewed"
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
        if prepared
        else "REMEDIATE_QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_renormalization_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_renormalization_assumption_reduction_packet_result_review_"
            "after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_PACKET_RESULT_"
            "ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares renormalization assumption-reduction analysis "
            "only. It consumes the accepted operator-domain closeout result "
            "review, preserves insufficient_assumptions_for_conservation, and "
            "does not discharge renormalization assumptions, construct a "
            "conservation proof object or witness, claim source admissibility "
            "or Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, promote the master "
            "action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_renormalization_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_renormalization_assumption_reduction_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR renormalization assumption-reduction packet."
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
    payload = write_qft_gr_renormalization_assumption_reduction_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_renormalization_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
