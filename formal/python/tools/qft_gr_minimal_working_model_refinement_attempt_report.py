from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_refinement_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
    REFINEMENT_OBJECTIVE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-13T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_20260613_v0"
ATTEMPT_ID = "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_EXECUTED_WITH_NO_"
    "SOURCE_ADMISSIBILITY_OR_CONSERVATION_PROOF"
)
RESULT_CLASSIFICATION = (
    "qft_gr_minimal_working_model_refinement_attempt_executed_with_domain_"
    "and_regularity_adjustment_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_working_model_refinement_attempt_result"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_refinement_attempt_result_review"
REFINEMENT_SCOPE = (
    "weak_pairing_domain_and_regularity_for_toy_candidate_without_source_admissibility"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_20260613_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded refinement attempt has been executed and must be "
                "reviewed before any conservation retest, source-admissibility "
                "claim, proof construction, or model promotion."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This bounded refinement-attempt target is consumed here.",
        },
        {
            "target": "retry_qft_gr_minimal_working_model_conservation_test",
            "decision": "not_authorized_pending_attempt_result_review",
            "reason": "The refinement attempt is not a conservation retest or proof.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains candidate-only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The adjustment records domain and regularity structure only.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by this attempt.",
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
            "reason": "QFT-GR closure remains outside this bounded refinement attempt.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _weak_pairing_domain_adjustment(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "adjustment_id": "toy_weak_pairing_domain_v1",
        "scope": "weak_pairing_domain",
        "refined_for": REFINEMENT_OBJECTIVE,
        "candidate_status": "candidate_only_not_source_admissibility",
        "test_vector_domain": (
            "compactly_supported_smooth_test_vectors_on_fixed_background_or_"
            "formal_surrogate"
        ),
        "dual_pairing_domain": (
            "toy_candidate_distributional_pairings_defined_only_for_recorded_"
            "test_vectors"
        ),
        "weak_divergence_pairing_form": (
            "pair_candidate_stress_energy_divergence_against_admitted_test_vector"
        ),
        "pairing_domain_status": "refined_for_attempt_not_source_admissibility",
        "source_domain_membership_claimed": False,
        "source_admissibility_claimed": False,
        "conservation_claimed": False,
        "conservation_test_retried": False,
        "review_refinement_focus": review.get("refinement_focus"),
    }


def _regularity_structure_adjustment() -> dict[str, Any]:
    return {
        "adjustment_id": "toy_regular_context_v1",
        "scope": "regularity",
        "refined_for": REFINEMENT_OBJECTIVE,
        "minimum_regular_context": (
            "toy_candidate_regular_enough_to_state_recorded_weak_pairings_only"
        ),
        "derivative_exchange_status": (
            "recorded_as_assumption_for_attempt_not_discharged_as_theorem"
        ),
        "boundary_control_status": (
            "recorded_as_packet_level_boundary_condition_not_global_discharge"
        ),
        "limit_interchange_status": (
            "recorded_as_regularization_assumption_not_conservation_proof"
        ),
        "weak_strong_scope_status": (
            "weak_distributional_scope_kept_separate_from_strong_pointwise_"
            "conservation"
        ),
        "regularity_discharge_claimed": False,
        "conservation_proof_object_constructed": False,
        "source_admissibility_claimed": False,
    }


def _obstruction_accounting() -> list[dict[str, Any]]:
    return [
        {
            "obstruction": "weak_pairing_domain_was_insufficiently_explicit",
            "refinement_component": "toy_weak_pairing_domain_v1",
            "status_after_attempt": (
                "domain_structure_refined_for_candidate_pairing_statement_only"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "obstruction": "derivative_exchange_regular_boundary_support_needed",
            "refinement_component": "toy_regular_context_v1",
            "status_after_attempt": (
                "regularity_budget_recorded_as_assumption_not_discharged_proof"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "obstruction": "limit_interchange_and_boundary_control_needed",
            "refinement_component": "toy_regular_context_v1",
            "status_after_attempt": (
                "limit_and_boundary_controls_scoped_to_attempt_not_global_claim"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
        {
            "obstruction": "weak_and_strong_conservation_scope_separation_needed",
            "refinement_component": "weak_distributional_scope_annotation",
            "status_after_attempt": (
                "weak_scope_preserved_without_strong_pointwise_conservation_claim"
            ),
            "source_admissibility_claimed": False,
            "conservation_claimed": False,
        },
    ]


def build_qft_gr_minimal_working_model_refinement_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    candidate_next_targets = _candidate_next_targets()
    domain_adjustment = _weak_pairing_domain_adjustment(review)
    regularity_adjustment = _regularity_structure_adjustment()
    obstruction_accounting = _obstruction_accounting()

    acceptance_criteria = {
        "consumes_expected_refinement_packet_result_review": review.get("schema_id")
        == EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID
        and review.get("review_id") == EXPECTED_PACKET_RESULT_REVIEW_ID,
        "packet_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
        "packet_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
        "packet_result_review_selected_this_attempt": review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "bounded_refinement_attempt_authorized": review.get(
            "bounded_refinement_attempt_authorized"
        )
        is True
        and review.get("refinement_attempt_authorized") is True,
        "review_did_not_execute_attempt": review.get(
            "bounded_refinement_attempt_executed_by_review"
        )
        is False
        and review.get("refinement_attempt_executed") is False,
        "candidate_only_status_preserved": review.get("toy_source_candidate_status")
        == "candidate_only_not_source_admissibility"
        and review.get("toy_source_candidate_remains_candidate_only") is True,
        "selected_refinement_objective_confirmed": review.get(
            "refinement_objective"
        )
        == REFINEMENT_OBJECTIVE
        and review.get("selected_refinement_target") == REFINEMENT_OBJECTIVE,
        "weak_pairing_domain_adjusted": domain_adjustment.get("scope")
        == "weak_pairing_domain"
        and domain_adjustment.get("source_admissibility_claimed") is False,
        "regularity_structure_adjusted": regularity_adjustment.get("scope")
        == "regularity"
        and regularity_adjustment.get("regularity_discharge_claimed") is False,
        "obstruction_accounting_recorded": len(obstruction_accounting) == 4
        and all(
            row["source_admissibility_claimed"] is False
            and row["conservation_claimed"] is False
            for row in obstruction_accounting
        ),
        "no_conservation_retry_or_test_result": review.get(
            "conservation_test_retried"
        )
        is False
        and review.get("conservation_test_result_claimed") is False
        and review.get("conservation_test_pass_claimed") is False,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_proof_or_witness": review.get(
            "conservation_claimed"
        )
        is False
        and review.get("conservation_proved") is False
        and review.get("conservation_proof_object_constructed") is False
        and review.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": review.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and review.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": review.get("qft_gr_seam_closed") is False
        and review.get("qft_gr_source_map_closure_claimed") is False,
        "no_empirical_validation_or_public_submission": review.get(
            "empirical_validation_claimed"
        )
        is False
        and review.get("public_submission_authorized") is False,
        "no_master_action_promotion": review.get("master_action_promoted") is False
        and review.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    executed = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": executed,
        "executed": executed,
        "attempt_executed": executed,
        "bounded_refinement_attempt_executed": executed,
        "refinement_attempt_executed": executed,
        "outcome_id": OUTCOME_ID
        if executed
        else "QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_REQUIRES_REMEDIATION",
        "result_classification": RESULT_CLASSIFICATION
        if executed
        else "qft_gr_minimal_working_model_refinement_attempt_requires_remediation",
        "attempt_classification": RESULT_CLASSIFICATION
        if executed
        else "qft_gr_minimal_working_model_refinement_attempt_requires_remediation",
        "result_classification_count": 1 if executed else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_refinement_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_refinement_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_packet_result_review_outcome_id": review.get("outcome_id"),
        "consumed_packet_result_review_classification": review.get(
            "result_review_classification"
        ),
        "candidate_only_status_preserved": executed,
        "toy_source_candidate_status": "candidate_only_not_source_admissibility",
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "refinement_objective": REFINEMENT_OBJECTIVE
        if executed
        else "requires_remediation",
        "selected_refinement_target": REFINEMENT_OBJECTIVE
        if executed
        else "requires_remediation",
        "selected_refinement_target_count": 1 if executed else 0,
        "refinement_scope": REFINEMENT_SCOPE,
        "refinement_focus": review.get("refinement_focus"),
        "weak_pairing_domain_adjustment": domain_adjustment,
        "regularity_structure_adjustment": regularity_adjustment,
        "obstruction_accounting": obstruction_accounting,
        "weak_pairing_domain_adjusted": executed,
        "regularity_structure_adjusted": executed,
        "refined_artifact_status": (
            "toy_candidate_refinement_attempt_executed_pending_result_review"
            if executed
            else "requires_remediation"
        ),
        "model_refinement_packet_prepared": review.get("model_refinement_packet_prepared")
        is True,
        "model_refinement_executed": executed,
        "bounded_refinement_attempt_result_review_pending": executed,
        "refinement_attempt_result_review_pending": executed,
        "conservation_test_retried": False,
        "conservation_test_executed_by_attempt": False,
        "conservation_test_result_claimed": False,
        "conservation_test_pass_claimed": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
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
        "aggregate_lean_timeout_caveat_preserved": review.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": review.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if executed
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT",
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_next_target_count": 1 if executed else 0,
        "selection_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_REFINEMENT_ATTEMPT_RESULT_"
            "ONLY_NO_CONSERVATION_RETRY_SOURCE_ADMISSIBILITY_CONSERVATION_"
            "PROOF_WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_"
            "EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This bounded refinement attempt adjusts only the weak pairing "
            "domain and regularity structure for the toy candidate. It does "
            "not retry the conservation test, does not claim source "
            "admissibility, does not claim conservation, constructs no "
            "conservation proof object or conservation witness, claims no "
            "Bianchi compatibility, derives no semiclassical Einstein equation, "
            "closes no QFT-GR seam, validates nothing empirically, authorizes "
            "no public submission, and promotes no master action. Boundary "
            "shorthand: no source admissibility, no conservation proof object, "
            "no conservation witness, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no QFT-GR closure, and no "
            "public submission."
        ),
    }


def write_qft_gr_minimal_working_model_refinement_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_refinement_attempt(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model bounded refinement "
            "attempt report."
        )
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_PACKET_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_working_model_refinement_attempt(
        packet_result_review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_refinement_attempt_report: "
        f"executed={payload['executed']} "
        f"classification={payload['result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
