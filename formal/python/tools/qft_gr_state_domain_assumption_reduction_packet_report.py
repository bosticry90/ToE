from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_OPERATOR_DOMAIN_CLOSEOUT_REVIEW_PATH,
)
from formal.python.tools.qft_gr_renormalization_assumption_reduction_closeout_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-07T00:00:00Z"
SCHEMA_ID = "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260607_v0"
PACKET_ID = "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_packet_prepared_with_no_"
    "conservation_witness_or_seam_closure"
)
BLOCKER = "insufficient_assumptions_for_conservation"
PRIOR_COMPLETED_FAMILIES = [
    "operator_domain_assumptions",
    "renormalization_assumptions",
]
SELECTED_ASSUMPTION_FAMILY = "state_domain_assumptions"
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "review_qft_gr_state_domain_assumption_reduction_packet_result"
STATE_DOMAIN_OBJECT = (
    "bounded_qft_state_domain_for_candidate_renormalized_stress_energy_expectation"
)
STATE_ADMISSIBILITY_BOUNDARY = (
    "state_admissibility_boundary_for_meaningful_renormalized_expectation_not_"
    "source_admissibility"
)
STATE_EXPECTATION_COMPATIBILITY = (
    "state_expectation_functional_compatible_with_operator_domain_and_"
    "renormalized_expectation_domain"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260607_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _available_repo_evidence() -> list[str]:
    return [
        "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_RESULT_REVIEW_v0",
        "QFT_GR_STATE_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
        "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
        "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_v0",
    ]


def _required_future_proof_objects() -> list[str]:
    return [
        "bounded_qft_state_domain_object_for_candidate_renormalized_source",
        "state_admissibility_boundary_for_meaningful_expectation_functional",
        "state_expectation_compatibility_with_operator_and_renormalization_domains",
        "state_domain_supports_future_conservation_proof_object_without_source_admissibility_claim",
    ]


def _candidate_reducible_assumptions() -> list[dict[str, Any]]:
    claim_ceiling = (
        "state_domain_assumption_reduction_analysis_only_no_conservation_"
        "proof_object_no_witness_no_source_admissibility"
    )
    return [
        {
            "assumption_id": "SD-ASSUMP-001-state_domain_object",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "supplied", "candidate_reducible"],
            "state_domain_object": STATE_DOMAIN_OBJECT,
            "available_repo_evidence": [
                "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_RESULT_REVIEW_v0",
                "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "bounded_qft_state_domain_object_for_candidate_renormalized_source"
            ),
            "candidate_reduction_route": (
                "pin the bounded QFT state domain where the candidate "
                "renormalized stress-energy expectation is meaningful, without "
                "claiming conservation or source admissibility"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "the candidate renormalized expectation may remain meaningful "
                "only for an unspecified state class"
            ),
        },
        {
            "assumption_id": "SD-ASSUMP-002-state_admissibility_boundary",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY,
            "available_repo_evidence": [
                "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_RESULT_REVIEW_v0",
                "QFT_GR_STRESS_ENERGY_CONSERVATION_OBSTRUCTION_REFINEMENT_PACKET_v0",
            ],
            "required_future_proof_object": (
                "state_admissibility_boundary_for_meaningful_expectation_functional"
            ),
            "candidate_reduction_route": (
                "separate state admissibility for expectation-meaningfulness "
                "from stress-energy source admissibility and Bianchi compatibility"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "state-domain admissibility remains conflated with downstream "
                "source-admissibility and conservation obligations"
            ),
        },
        {
            "assumption_id": "SD-ASSUMP-003-state_expectation_compatibility",
            "assumption_family": SELECTED_ASSUMPTION_FAMILY,
            "current_status": ["required", "missing", "candidate_reducible"],
            "state_expectation_compatibility": STATE_EXPECTATION_COMPATIBILITY,
            "available_repo_evidence": [
                "QFT_GR_STATE_EXPECTATION_DOMAIN_LINK_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
                "QFT_GR_RENORMALIZED_EXPECTATION_DOMAIN_ASSUMPTION_REDUCTION_ATTEMPT_RESULT_REVIEW_v0",
                "QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
            ],
            "required_future_proof_object": (
                "state_expectation_compatibility_with_operator_and_renormalization_domains"
            ),
            "candidate_reduction_route": (
                "bind the supplied state-expectation functional to the accepted "
                "operator-domain and renormalization-domain reductions without "
                "asserting a conserved source"
            ),
            "claim_ceiling": claim_ceiling,
            "failure_mode_if_unresolved": (
                "operator-domain and renormalization reductions may not share a "
                "common state-expectation domain for a future conservation proof"
            ),
        },
    ]


def _not_reducible_in_current_lane() -> list[dict[str, str]]:
    return [
        {
            "assumption_id": "SD-NONRED-001-state-domain-discharge",
            "reason": "This packet prepares state-domain analysis only and does not discharge the family.",
        },
        {
            "assumption_id": "SD-NONRED-002-conservation-proof-object",
            "reason": "A conservation proof object remains downstream of state-domain assumption reduction.",
        },
        {
            "assumption_id": "SD-NONRED-003-conservation-witness",
            "reason": "No conservation witness is constructed or authorized by this packet.",
        },
        {
            "assumption_id": "SD-NONRED-004-source-admissibility",
            "reason": "State-domain admissibility for expectations is not stress-energy source admissibility.",
        },
        {
            "assumption_id": "SD-NONRED-005-bianchi-compatibility",
            "reason": "Bianchi compatibility remains a downstream geometric obligation.",
        },
        {
            "assumption_id": "SD-NONRED-006-semiclassical-einstein-equation",
            "reason": "The semiclassical Einstein equation is not derived by state-domain packet preparation.",
        },
        {
            "assumption_id": "SD-NONRED-007-qft-gr-seam-closure",
            "reason": "State-domain assumption reduction cannot close the QFT-GR seam.",
        },
        {
            "assumption_id": "SD-NONRED-008-release-or-public-submission",
            "reason": "Release assembly and public submission are outside this bounded packet.",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared state-domain assumption-reduction packet must be "
                "result-reviewed before any bounded reduction attempt or "
                "downstream assumption-family selection is authorized."
            ),
        },
        {
            "target": "execute_qft_gr_state_domain_assumption_reduction_attempt",
            "decision": "deferred",
            "reason": "A bounded state-domain reduction attempt requires packet result review first.",
        },
        {
            "target": "prepare_qft_gr_mathematical_regularity_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Mathematical regularity remains outside this state-domain packet preparation.",
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": "State-domain preparation does not authorize source-admissibility reduction.",
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
            "reason": "State-domain assumptions alone do not imply source admissibility.",
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
            "reason": "Release assembly and public submission are outside this bounded checkpoint.",
        },
    ]


def build_qft_gr_state_domain_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    operator_domain_closeout_review_path: Path = DEFAULT_OPERATOR_DOMAIN_CLOSEOUT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    operator_domain_review = _read_json(operator_domain_closeout_review_path)
    candidate_reducible = _candidate_reducible_assumptions()
    not_reducible = _not_reducible_in_current_lane()
    candidate_next_targets = _candidate_next_targets()

    acceptance_criteria = {
        "consumes_expected_renormalization_closeout_result_review": result_review.get(
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
        "preserves_packet_vs_review_target_split": result_review.get(
            "renormalization_assumption_reduction_closeout_packet_selected_next_target"
        )
        == "review_qft_gr_renormalization_assumption_reduction_closeout_packet_result"
        and result_review.get(
            "renormalization_assumption_reduction_closeout_packet_result_review_selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == BLOCKER
        and result_review.get("conservation_blocker_remains") is True,
        "prior_operator_domain_family_completed_for_lane": operator_domain_review.get(
            "operator_domain_assumptions_closed_for_this_lane"
        )
        is True
        and operator_domain_review.get("accepted_operator_domain_assumption_row_count")
        == 6,
        "prior_renormalization_family_completed_for_lane": result_review.get(
            "renormalization_assumptions_closed_for_this_lane"
        )
        is True
        and result_review.get("accepted_renormalization_assumption_row_count") == 5,
        "selects_only_state_domain_assumptions": result_review.get(
            "next_assumption_family"
        )
        == SELECTED_ASSUMPTION_FAMILY
        and result_review.get("state_domain_assumption_reduction_packet_authorized")
        is True,
        "required_packet_fields_prepared": all(
            [
                STATE_DOMAIN_OBJECT,
                STATE_ADMISSIBILITY_BOUNDARY,
                STATE_EXPECTATION_COMPATIBILITY,
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
        "does_not_discharge_state_domain_assumptions": True,
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
        else "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_renormalization_assumption_reduction_closeout_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_qft_gr_renormalization_assumption_reduction_closeout_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "supporting_operator_domain_closeout_result_review": operator_domain_review.get(
            "review_id"
        ),
        "supporting_operator_domain_closeout_result_review_pointer": _ptr(
            operator_domain_closeout_review_path
        ),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "completed_prior_assumption_families": PRIOR_COMPLETED_FAMILIES,
        "completed_prior_assumption_family_count": len(PRIOR_COMPLETED_FAMILIES),
        "prior_completed_operator_domain_assumption_rows": operator_domain_review.get(
            "accepted_operator_domain_assumption_rows", []
        ),
        "prior_completed_operator_domain_assumption_row_count": operator_domain_review.get(
            "accepted_operator_domain_assumption_row_count"
        ),
        "prior_completed_renormalization_assumption_rows": result_review.get(
            "accepted_renormalization_assumption_rows", []
        ),
        "prior_completed_renormalization_assumption_row_count": result_review.get(
            "accepted_renormalization_assumption_row_count"
        ),
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "selected_family_only": True,
        "state_domain_object": STATE_DOMAIN_OBJECT,
        "state_admissibility_boundary": STATE_ADMISSIBILITY_BOUNDARY,
        "state_expectation_compatibility": STATE_EXPECTATION_COMPATIBILITY,
        "available_repo_evidence": _available_repo_evidence(),
        "required_future_proof_objects": _required_future_proof_objects(),
        "candidate_reducible_assumptions": candidate_reducible,
        "candidate_reducible_assumption_count": len(candidate_reducible),
        "not_reducible_in_current_lane": not_reducible,
        "not_reducible_in_current_lane_count": len(not_reducible),
        "state_domain_assumption_reduction_analysis_prepared": prepared,
        "prepares_reduction_analysis_only": prepared,
        "state_domain_assumptions_discharged": False,
        "state_domain_assumptions_reduced_or_discharged_by_preparation": False,
        "state_admissibility_claimed_as_source_admissibility": False,
        "claim_ceiling": (
            "state_domain_assumption_reduction_packet_preparation_only_no_"
            "conservation_witness_no_conservation_proof_object_no_source_"
            "admissibility_no_bianchi_no_qft_gr_seam_closure"
        ),
        "failure_mode_if_unresolved": (
            "operator-domain and renormalization assumptions are closed only "
            "for this lane, but the conservation blocker remains because the "
            "state domain, state admissibility boundary, and state-expectation "
            "compatibility are not yet result-reviewed"
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
        else "REMEDIATE_QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_state_domain_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_state_domain_assumption_reduction_packet_result_review_after_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_ONLY_"
            "NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only state-domain assumption-reduction "
            "analysis. It records the state/domain object, state admissibility "
            "boundary, state-expectation compatibility, available repo "
            "evidence, required future proof objects, candidate reduction "
            "route, claim ceiling, and failure mode. It does not prove "
            "conservation, construct a conservation proof object or "
            "conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_state_domain_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    operator_domain_closeout_review_path: Path = DEFAULT_OPERATOR_DOMAIN_CLOSEOUT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_state_domain_assumption_reduction_packet(
        result_review_path=result_review_path,
        operator_domain_closeout_review_path=operator_domain_closeout_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR state-domain assumption-reduction packet."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument(
        "--operator-domain-closeout-review",
        type=Path,
        default=DEFAULT_OPERATOR_DOMAIN_CLOSEOUT_REVIEW_PATH,
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
    operator_domain_closeout_review_path = (
        ns.operator_domain_closeout_review
        if ns.operator_domain_closeout_review.is_absolute()
        else (REPO_ROOT / ns.operator_domain_closeout_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_state_domain_assumption_reduction_packet(
        result_review_path=result_review_path,
        operator_domain_closeout_review_path=operator_domain_closeout_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_state_domain_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} family={payload['selected_assumption_family']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
