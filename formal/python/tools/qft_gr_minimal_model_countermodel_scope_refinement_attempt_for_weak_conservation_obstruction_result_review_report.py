from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    NOT_FOUND_CLASSIFICATION,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_20260615_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_ACCEPTS_REFINED_COUNTERMODEL_"
    "SCOPE_AND_AUTHORIZES_BOUNDED_COUNTERMODEL_REATTEMPT_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_"
    "conservation_obstruction_result_review_accepts_refined_countermodel_scope_"
    "and_authorizes_bounded_countermodel_reattempt_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_"
    "conservation_obstruction"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_"
    "obstruction_preparation"
)
COUNTERMODEL_REATTEMPT_TARGET = (
    "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_"
    "for_weak_conservation_obstruction"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_WEAK_"
        "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_20260615_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalModelCountermodelScopeRefinementAttemptForWeakConservation"
        "ObstructionResultReview.lean"
    )
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
                "The refined countermodel scope is accepted, so the only "
                "authorized next action is preparation of a bounded "
                "countermodel reattempt packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "The scope-refinement-attempt result-review target is consumed "
                "here."
            ),
        },
        {
            "target": COUNTERMODEL_REATTEMPT_TARGET,
            "decision": "not_authorized_until_countermodel_reattempt_packet_review",
            "reason": (
                "A countermodel/no-go reattempt remains downstream of a "
                "prepared and reviewed reattempt packet."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_review",
            "reason": (
                "Source-map ladder work remains downstream unless the later "
                "bounded reattempt selects not-found or source-map-ladder "
                "pressure."
            ),
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "The review accepts refined scope only; no countermodel is found.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is found or claimed by this review.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "The refined-scope review does not evaluate not-found status.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The pinned source/test pair remains candidate-only.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened by this review.",
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
            "reason": "The review authorizes a packet only, not QFT-GR closure.",
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


def _review_findings() -> list[str]:
    return [
        (
            "The bounded scope-refinement attempt consumed the accepted packet "
            "review and executed only the authorized refined-scope lane."
        ),
        (
            "The attempt pins the broader source/test instantiation, partial "
            "weak-pairing contract, and divergence/boundary/curvature "
            "evaluation protocol for a later bounded reattempt."
        ),
        (
            "The later found, not-found, and inconclusive criteria are defined "
            "under the refined scope, but none is selected by this review."
        ),
        (
            "The review authorizes only a bounded reattempt packet; it does "
            "not prepare or execute the reattempt."
        ),
        (
            "The strict toy positive witness remains valid under its strict "
            "antecedents and is not refuted by the broader refined scope."
        ),
    ]


def _validation_policy(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_scope_refinement_attempt_result_review",
        "routine_result_review_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_scope_refinement_attempt_validation_policy": attempt.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(attempt)
    decisive_criteria = attempt.get("decisive_classification_criteria", [])
    decisive_classes = {row.get("classification") for row in decisive_criteria}

    acceptance_criteria = {
        "consumes_expected_scope_refinement_attempt": (
            attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID
            and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
            and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME
            and attempt.get("result_classification")
            == EXPECTED_ATTEMPT_CLASSIFICATION
            and attempt.get("selected_next_target") == CONSUMED_TARGET
        ),
        "attempt_executed_and_accepted_pending_review": (
            attempt.get("executed") is True
            and attempt.get("accepted") is True
            and attempt.get("scope_refinement_attempt_executed") is True
            and attempt.get("scope_refinement_attempt_result_review_pending")
            is True
            and attempt.get("scope_refinement_attempt_result_reviewed") is False
        ),
        "refined_scope_pinned": (
            attempt.get("countermodel_lane_decidability_scope_pinned") is True
            and attempt.get("source_test_instantiation_pinned") is True
            and attempt.get("weak_pairing_semantics_pinned") is True
            and attempt.get("broader_divergence_boundary_evaluation_scope_pinned")
            is True
            and attempt.get("pinned_source_test_pair_id") == PINNED_SOURCE_TEST_PAIR_ID
            and attempt.get("pinned_weak_pairing_contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and attempt.get("pinned_evaluation_scope_id") == PINNED_EVALUATION_SCOPE_ID
        ),
        "refined_scope_payloads_present": (
            attempt.get("source_test_instantiation", {}).get("instantiation_id")
            == PINNED_SOURCE_TEST_PAIR_ID
            and attempt.get("weak_pairing_semantics", {}).get("contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and attempt.get("weak_pairing_semantics", {}).get("partiality_pinned")
            == "yes"
            and attempt.get("weak_pairing_semantics", {}).get("totality_claimed")
            == "no"
            and attempt.get("evaluation_scope", {}).get("evaluation_scope_id")
            == PINNED_EVALUATION_SCOPE_ID
            and attempt.get("evaluation_scope", {}).get("probe_count") == 5
        ),
        "decisive_criteria_defined_without_selecting_result": (
            attempt.get("decisive_classification_criteria_count") == 3
            and len(decisive_criteria) == 3
            and decisive_classes
            == {
                FOUND_CLASSIFICATION,
                NOT_FOUND_CLASSIFICATION,
                INCONCLUSIVE_CLASSIFICATION,
            }
            and all(row.get("selected_now") == "no" for row in decisive_criteria)
            and attempt.get("selected_countermodel_criterion_count") == 0
            and attempt.get("selected_no_go_criterion_count") == 0
        ),
        "strict_toy_witness_preserved_not_refuted": (
            attempt.get("strict_toy_witness_preserved") is True
            and attempt.get("strict_toy_witness_accepted") is True
            and attempt.get("strict_toy_assumptions_only") is True
            and attempt.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "obstruction_candidate_carried_unresolved": (
            attempt.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and attempt.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and attempt.get("obstruction_status") == OBSTRUCTION_STATUS
            and attempt.get("dominant_obstruction_resolved") is False
            and attempt.get("mathematical_resolution_claimed") is False
        ),
        "review_selects_reattempt_packet_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "does_not_prepare_or_execute_reattempt": (
            attempt.get("countermodel_attempt_after_scope_refinement_authorized")
            is False
            and attempt.get("countermodel_attempt_after_scope_refinement_executed")
            is False
            and attempt.get("countermodel_attempt_reauthorized") is False
            and attempt.get("countermodel_attempt_reexecuted") is False
        ),
        "no_countermodel_no_go_not_found_or_inconclusive_result_claim": (
            attempt.get("countermodel_result_claimed") is False
            and attempt.get("countermodel_exists_claimed") is False
            and attempt.get("countermodel_achieved") is False
            and attempt.get("no_go_result_claimed") is False
            and attempt.get("not_found_result_claimed") is False
            and attempt.get("inconclusive_result_claimed") is False
        ),
        "no_source_admissibility_or_broad_conservation": (
            attempt.get("source_admissibility_claimed") is False
            and attempt.get("stress_energy_source_admissibility_claimed") is False
            and attempt.get("physical_source_claimed") is False
            and attempt.get("conservation_claimed") is False
            and attempt.get("conservation_proved") is False
            and attempt.get("conservation_proof_object_constructed") is False
            and attempt.get("conservation_witness_constructed") is False
            and attempt.get("full_qft_gr_conservation_claimed") is False
            and attempt.get("unbounded_conservation_proved") is False
        ),
        "no_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            attempt.get("Bianchi_compatibility_claimed") is False
            and attempt.get("semiclassical_einstein_equation_derived") is False
            and attempt.get("qft_gr_seam_closed") is False
            and attempt.get("qft_gr_source_map_closure_claimed") is False
            and attempt.get("empirical_validation_claimed") is False
            and attempt.get("public_submission_authorized") is False
            and attempt.get("master_action_promoted") is False
            and attempt.get("master_action_promotion_authorized") is False
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
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_"
            "ATTEMPT_FOR_WEAK_CONSERVATION_OBSTRUCTION_RESULT_REVIEW"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_ATTEMPT_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_"
            "weak_conservation_obstruction_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_scope_refinement_attempt_id": EXPECTED_ATTEMPT_ID,
        "consumes_scope_refinement_attempt_pointer": _ptr(attempt_path),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "scope_refinement_attempt_result_review_accepted": accepted,
        "scope_refinement_attempt_consumed": accepted,
        "scope_refinement_attempt_accepted": accepted,
        "scope_refinement_attempt_result_reviewed": accepted,
        "scope_refinement_attempt_result_review_pending": False,
        "scope_refinement_attempt_executed": (
            attempt.get("scope_refinement_attempt_executed") is True
        ),
        "countermodel_lane_decidability_scope_accepted": accepted,
        "countermodel_lane_decidability_scope_pinned": (
            attempt.get("countermodel_lane_decidability_scope_pinned") is True
        ),
        "source_test_instantiation_pinned": (
            attempt.get("source_test_instantiation_pinned") is True
        ),
        "weak_pairing_semantics_pinned": (
            attempt.get("weak_pairing_semantics_pinned") is True
        ),
        "broader_divergence_boundary_evaluation_scope_pinned": (
            attempt.get("broader_divergence_boundary_evaluation_scope_pinned") is True
        ),
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": attempt.get("source_test_instantiation", {}),
        "weak_pairing_semantics": attempt.get("weak_pairing_semantics", {}),
        "evaluation_scope": attempt.get("evaluation_scope", {}),
        "decisive_classification_criteria": decisive_criteria,
        "decisive_classification_criteria_count": len(decisive_criteria),
        "decisive_found_classification": FOUND_CLASSIFICATION,
        "decisive_not_found_classification": NOT_FOUND_CLASSIFICATION,
        "decisive_inconclusive_classification": INCONCLUSIVE_CLASSIFICATION,
        "found_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "inconclusive_classification_not_selected": True,
        "selected_countermodel_criterion_count": 0,
        "selected_no_go_criterion_count": 0,
        "countermodel_reattempt_packet_authorized": accepted,
        "bounded_countermodel_reattempt_packet_authorized_only": accepted,
        "countermodel_reattempt_packet_prepared": False,
        "countermodel_reattempt_packet_result_review_pending": False,
        "countermodel_reattempt_executed": False,
        "countermodel_attempt_after_scope_refinement_authorized": False,
        "countermodel_attempt_after_scope_refinement_executed": False,
        "countermodel_attempt_reauthorized": False,
        "countermodel_attempt_reexecuted": False,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": attempt.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "scope_refinement_attempt_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
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
        "review_findings": _review_findings(),
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_result_review_current_target_registry_gate": (
                "required_for_checkpoint"
            ),
            "adjacent_qft_gr_nonclaim_gates": "required_bounded_subset",
            "targeted_lean_result_review_frontier_import_checks": (
                "required_for_checkpoint"
            ),
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
            "required for this routine bounded scope-refinement-attempt result-"
            "review checkpoint. The release-index path remains not freshly "
            "Lean-validated, aggregate Lean is not run, and no aggregate Lean "
            "health claim is made."
        ),
        "lean_attempt_file": _ptr(LEAN_ATTEMPT_PATH),
        "lean_result_review_file": _ptr(LEAN_REVIEW_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION_ONLY_NO_COUNTERMODEL_RESULT_CLAIM_"
            "NO_NO_GO_RESULT_CLAIM_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_"
            "PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the refined countermodel scope "
            "from the bounded scope-refinement attempt and authorizes only a "
            "bounded countermodel reattempt packet. It does not prepare or "
            "execute a reattempt, does not claim a countermodel result, does "
            "not claim a no-go result, does not claim a not-found result, does "
            "not refute the accepted strict toy witness, preserves no source "
            "admissibility, no Bianchi compatibility, no semiclassical "
            "Einstein equation, no broad QFT-GR conservation, no QFT-GR "
            "closure, no empirical validation, no public submission, and no "
            "master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the bounded QFT-GR minimal model countermodel scope-"
            "refinement attempt result review for the weak-conservation "
            "obstruction."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "review_id": payload["review_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "result_review_classification": payload[
                    "result_review_classification"
                ],
                "accepted": payload["accepted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
