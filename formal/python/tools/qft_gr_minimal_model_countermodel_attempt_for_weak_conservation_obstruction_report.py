from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_20260615_v0"
)
ATTEMPT_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
FOUND_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
    "found_pending_result_review"
)
NOT_FOUND_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
    "not_found_requires_source_map_ladder"
)
INCONCLUSIVE_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
    "inconclusive_requires_countermodel_scope_refinement"
)
RESULT_CLASSIFICATION = INCONCLUSIVE_CLASSIFICATION
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
    "obstruction_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
    "obstruction_result_review"
)
COUNTERMODEL_SCOPE_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_"
    "weak_conservation_obstruction"
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelAttemptForWeakConservationObstruction.lean"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_20260615_v0.json"
    )
)


EXPECTED_CRITERION_IDS = {
    "candidate_pairing_domain_undefined",
    "allowed_test_exposes_nonzero_weak_divergence",
    "derivative_exchange_not_justified",
    "boundary_term_survives_without_compact_support",
    "divergence_identity_not_derivable",
    "test_vector_class_mismatch",
    "curvature_coupling_leaves_uncancelled_term",
}


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _classification_options() -> list[str]:
    return [
        FOUND_CLASSIFICATION,
        NOT_FOUND_CLASSIFICATION,
        INCONCLUSIVE_CLASSIFICATION,
    ]


def _classification_rows() -> list[dict[str, Any]]:
    return [
        {
            "classification": FOUND_CLASSIFICATION,
            "selected": False,
            "meaning": (
                "A concrete allowed broader source/test configuration would "
                "have to satisfy one of the packet's countermodel criteria."
            ),
        },
        {
            "classification": NOT_FOUND_CLASSIFICATION,
            "selected": False,
            "meaning": (
                "The attempt would have to exhaust the prepared broader "
                "countermodel scope before routing to source-map ladder work."
            ),
        },
        {
            "classification": INCONCLUSIVE_CLASSIFICATION,
            "selected": True,
            "meaning": (
                "The prepared criteria were tested against the current broader "
                "weak-pairing/source-candidate family, but the family lacks a "
                "concrete broader source/test instantiation and total pairing "
                "scope needed to decide found or not-found status."
            ),
        },
    ]


def _criteria_assessment(criteria: list[dict[str, str]]) -> list[dict[str, str]]:
    by_id = {row["criterion_id"]: row for row in criteria}
    statuses = {
        "candidate_pairing_domain_undefined": (
            "not_selected_requires_concrete_broader_source_test_pair"
        ),
        "allowed_test_exposes_nonzero_weak_divergence": (
            "not_selected_requires_evaluated_broader_divergence_pairing"
        ),
        "derivative_exchange_not_justified": (
            "pressure_retained_not_promoted_to_no_go_result"
        ),
        "boundary_term_survives_without_compact_support": (
            "pressure_retained_requires_boundary_semantics_refinement"
        ),
        "divergence_identity_not_derivable": (
            "pressure_retained_requires_source_map_or_identity_derivation_scope"
        ),
        "test_vector_class_mismatch": (
            "pressure_retained_requires_broader_test_class_instantiation"
        ),
        "curvature_coupling_leaves_uncancelled_term": (
            "pressure_retained_requires_curvature_coupling_scope_refinement"
        ),
    }
    return [
        {
            "criterion_id": criterion_id,
            "packet_result_kind": by_id.get(criterion_id, {}).get("result_kind", ""),
            "attempt_status": statuses[criterion_id],
            "selected_as_countermodel_or_no_go_result": "no",
        }
        for criterion_id in sorted(EXPECTED_CRITERION_IDS)
    ]


def _attempt_findings() -> list[str]:
    return [
        (
            "The attempt consumes the accepted countermodel packet result review "
            "and executes only the authorized bounded countermodel-attempt lane."
        ),
        (
            "All seven prepared countermodel/no-go criteria are checked as "
            "scope criteria for the broader weak-pairing/source-candidate family."
        ),
        (
            "No concrete broader source/test pair with pinned weak-pairing "
            "semantics is available in the current packet scope."
        ),
        (
            "The undefined-pairing, nonzero-divergence, derivative-exchange, "
            "boundary, identity, test-class, and curvature-coupling pressures "
            "therefore remain pressure points rather than selected countermodel "
            "or no-go results."
        ),
        (
            "The strict toy positive witness remains valid under its strict "
            "antecedents and is not refuted by this inconclusive broader-family "
            "attempt."
        ),
    ]


def _scope_refinement_requirements() -> list[dict[str, str]]:
    return [
        {
            "requirement_id": "concrete_broader_source_test_pair",
            "reason": (
                "A found/not-found attempt needs an explicit broader "
                "candidate source and broader allowed test object."
            ),
        },
        {
            "requirement_id": "weak_pairing_totality_or_partiality_contract",
            "reason": (
                "The attempt needs a pinned rule for when the broader weak "
                "pairing is defined, partial, or undefined."
            ),
        },
        {
            "requirement_id": "broader_divergence_or_boundary_evaluation_scope",
            "reason": (
                "The attempt needs enough semantics to decide whether the "
                "broader weak divergence, boundary term, or curvature-coupling "
                "term vanishes."
            ),
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded attempt executed and selected an inconclusive "
                "classification, so the only next action is result review."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The countermodel attempt execution target is consumed here.",
        },
        {
            "target": COUNTERMODEL_SCOPE_REFINEMENT_TARGET,
            "decision": "candidate_after_result_review_accepts_inconclusive",
            "reason": (
                "Scope refinement is the follow-on route only if result review "
                "accepts the inconclusive classification."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_attempt",
            "reason": (
                "Source-map ladder work remains a later route, but the attempt "
                "does not select it before result review."
            ),
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "No countermodel-found classification is selected.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is selected or reviewed.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The attempt does not establish source admissibility.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened by this attempt.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "No semiclassical Einstein equation is derived.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "The countermodel attempt does not close QFT-GR.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
        {
            "target": "promote_master_action",
            "decision": "not_authorized",
            "reason": "No master-action promotion is authorized.",
        },
    ]


def _validation_policy(result_review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_attempt_execution",
        "routine_attempt_uses_bounded_target_relevant_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "long_running_validation_escalation_authorized": False,
        "timeout_rerun_loop_authorized": False,
        "timeout_recorded_as_caveat_not_rerun_instruction": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "inherited_countermodel_packet_result_review_validation_policy": result_review.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    criteria = result_review.get("countermodel_or_no_go_criteria", [])
    criteria_assessment = _criteria_assessment(criteria)
    classification_rows = _classification_rows()
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(result_review)

    criteria_ids = {row.get("criterion_id") for row in criteria}
    selected_classifications = [
        row["classification"] for row in classification_rows if row["selected"] is True
    ]

    acceptance_criteria = {
        "consumes_expected_countermodel_packet_result_review": (
            result_review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and result_review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and result_review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and result_review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and result_review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "packet_result_review_authorized_this_attempt_only": (
            result_review.get("accepted") is True
            and result_review.get("bounded_countermodel_attempt_authorized_only")
            is True
            and result_review.get("countermodel_attempt_authorized") is True
            and result_review.get("countermodel_attempt_executed") is False
        ),
        "countermodel_or_no_go_criteria_loaded": (
            result_review.get("countermodel_or_no_go_criteria_count") == 7
            and len(criteria) == 7
            and criteria_ids == EXPECTED_CRITERION_IDS
        ),
        "attempt_evaluates_all_criteria_without_selecting_countermodel_or_no_go": (
            len(criteria_assessment) == 7
            and {
                row["criterion_id"] for row in criteria_assessment
            }
            == EXPECTED_CRITERION_IDS
            and all(
                row["selected_as_countermodel_or_no_go_result"] == "no"
                for row in criteria_assessment
            )
        ),
        "classification_authorized_and_exactly_one_selected": (
            RESULT_CLASSIFICATION in _classification_options()
            and selected_classifications == [RESULT_CLASSIFICATION]
        ),
        "attempt_classified_inconclusive_pending_review": (
            RESULT_CLASSIFICATION == INCONCLUSIVE_CLASSIFICATION
            and FOUND_CLASSIFICATION not in selected_classifications
            and NOT_FOUND_CLASSIFICATION not in selected_classifications
        ),
        "strict_toy_witness_preserved_not_refuted": (
            result_review.get("strict_toy_witness_preserved") is True
            and result_review.get("strict_toy_witness_accepted") is True
            and result_review.get("strict_toy_assumptions_only") is True
            and result_review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "obstruction_candidate_carried_unresolved": (
            result_review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and result_review.get("canonical_obstruction_id")
            == CANONICAL_OBSTRUCTION_ID
            and result_review.get("obstruction_status") == OBSTRUCTION_STATUS
            and result_review.get("dominant_obstruction_resolved") is False
            and result_review.get("mathematical_resolution_claimed") is False
        ),
        "attempt_selects_result_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "no_countermodel_no_go_or_source_admissibility_claim": (
            result_review.get("countermodel_result_claimed") is False
            and result_review.get("countermodel_achieved") is False
            and result_review.get("no_go_result_claimed") is False
            and result_review.get("source_admissibility_claimed") is False
            and result_review.get("stress_energy_source_admissibility_claimed")
            is False
        ),
        "no_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            result_review.get("Bianchi_compatibility_claimed") is False
            and result_review.get("semiclassical_einstein_equation_derived")
            is False
            and result_review.get("qft_gr_seam_closed") is False
            and result_review.get("qft_gr_source_map_closure_claimed") is False
            and result_review.get("empirical_validation_claimed") is False
            and result_review.get("public_submission_authorized") is False
            and result_review.get("master_action_promoted") is False
            and result_review.get("master_action_promotion_authorized") is False
        ),
        "routine_validation_policy_preserves_non_escalation": all(
            validation_policy[key] is False
            for key in [
                "full_pytest_required",
                "full_governance_suite_required",
                "full_aggregate_lean_required",
                "full_ci_parity_required",
                "full_security_scan_required",
                "long_running_validation_escalation_authorized",
                "timeout_rerun_loop_authorized",
                "aggregate_lean_health_claimed",
            ]
        ),
    }
    executed = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if executed
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": executed,
        "accepted": executed,
        "attempt_decision": "executed" if executed else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if executed
        else (
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
            "OBSTRUCTION_REQUIRES_REMEDIATION"
        ),
        "result_classification": RESULT_CLASSIFICATION
        if executed
        else INCONCLUSIVE_CLASSIFICATION,
        "selected_classification": RESULT_CLASSIFICATION
        if executed
        else INCONCLUSIVE_CLASSIFICATION,
        "classification_options": _classification_options(),
        "classification_rows": classification_rows,
        "result_classification_count": 1 if executed else 0,
        "selected_classification_count": 1 if executed else 0,
        "found_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "consumed_target": CONSUMED_TARGET,
        "consumes_countermodel_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_countermodel_packet_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "countermodel_packet_result_review_accepted": result_review.get("accepted"),
        "bounded_countermodel_attempt_authorized_only": result_review.get(
            "bounded_countermodel_attempt_authorized_only"
        ),
        "countermodel_attempt_authorized": result_review.get(
            "countermodel_attempt_authorized"
        ),
        "countermodel_attempt_executed": executed,
        "countermodel_attempt_result_reviewed": False,
        "countermodel_attempt_result_review_pending": executed,
        "countermodel_attempt_classified_inconclusive_pending_result_review": executed,
        "countermodel_attempt_is_not_strict_toy_witness_refutation": True,
        "countermodel_found_pending_result_review": False,
        "countermodel_not_found_requires_source_map_ladder": False,
        "countermodel_scope_refinement_required_pending_result_review": executed,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": result_review.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "countermodel_or_no_go_criteria": criteria,
        "countermodel_or_no_go_criteria_count": len(criteria),
        "criteria_assessment": criteria_assessment,
        "selected_countermodel_criterion_count": 0,
        "selected_no_go_criterion_count": 0,
        "attempt_findings": _attempt_findings(),
        "scope_refinement_requirements": _scope_refinement_requirements(),
        "scope_refinement_requirement_count": 3,
        "countermodel_scope_refinement_lane_retained_as_follow_on": True,
        "countermodel_scope_refinement_packet_authorized": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "source_admissibility_can_be_considered": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "full_qft_gr_conservation_claimed": False,
        "unbounded_conservation_proved": False,
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
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_attempt_current_target_registry_gate": "required_for_checkpoint",
            "adjacent_qft_gr_nonclaim_gates": "required_bounded_subset",
            "targeted_lean_attempt_frontier_import_checks": "required_for_checkpoint",
            "git_diff_check": "required_for_checkpoint",
            "full_pytest": "not_required_for_checkpoint",
            "full_governance_suite": "not_required_for_checkpoint",
            "full_aggregate_lean": "not_required_for_checkpoint_preserved_caveat",
            "release_index_lean_path": "not_freshly_validated_preserved_caveat",
            "full_ci_parity": "not_required_for_checkpoint",
            "security_scan": "not_required_for_checkpoint",
        },
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded countermodel-attempt checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "lean_attempt_file": _ptr(LEAN_ATTEMPT_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "attempt_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if executed else 0,
        "selected_next_target_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION_RESULT_ONLY_NO_COUNTERMODEL_RESULT_CLAIM_"
            "NO_NO_GO_RESULT_CLAIM_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_"
            "PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This bounded countermodel attempt executes only the authorized "
            "criteria check against the broader weak-pairing/source-candidate "
            "family and records an inconclusive classification pending result "
            "review because the current scope lacks a concrete broader "
            "source/test instantiation and pinned weak-pairing semantics. It "
            "does not claim a countermodel result, does not claim a no-go "
            "result, does not refute the accepted strict toy witness, preserves "
            "no source admissibility, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no broad QFT-GR conservation, "
            "no QFT-GR closure, no empirical validation, no public submission, "
            "and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the bounded QFT-GR minimal model countermodel attempt "
            "for the weak-conservation obstruction."
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
    payload = write_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "attempt_id": payload["attempt_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "result_classification": payload["result_classification"],
                "executed": payload["executed"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
