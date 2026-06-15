from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    CANONICAL_OBSTRUCTION_ID,
    COUNTERMODEL_SCOPE_REFINEMENT_TARGET,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    NOT_FOUND_CLASSIFICATION,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_RESULT_REVIEW_20260615_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_RESULT_REVIEW_ACCEPTS_INCONCLUSIVE_COUNTERMODEL_ATTEMPT_AND_"
    "AUTHORIZES_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
    "obstruction_result_review_accepts_inconclusive_countermodel_attempt_and_"
    "authorizes_countermodel_scope_refinement_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = COUNTERMODEL_SCOPE_REFINEMENT_TARGET
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_"
    "conservation_obstruction_preparation"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_RESULT_REVIEW_20260615_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelAttemptForWeakConservationObstructionResultReview.lean"
)

EXPECTED_SCOPE_REQUIREMENT_IDS = {
    "concrete_broader_source_test_pair",
    "weak_pairing_totality_or_partiality_contract",
    "broader_divergence_or_boundary_evaluation_scope",
}


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
                "The bounded attempt is accepted as inconclusive, so the only "
                "authorized next action is preparation of a countermodel scope-"
                "refinement packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The countermodel-attempt result-review target is consumed here.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_review",
            "reason": (
                "Source-map ladder work remains downstream, but the accepted "
                "inconclusive attempt first requires concrete source/test and "
                "weak-pairing scope refinement."
            ),
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "The found-countermodel classification was not selected.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result was selected by the attempt or this review.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "The not-found/source-map-ladder classification was not selected.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The review does not establish any admissible source map.",
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
            "reason": "The review authorizes refinement only, not QFT-GR closure.",
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
            "The bounded countermodel attempt consumed the accepted packet "
            "review and executed only the authorized criteria check."
        ),
        (
            "The selected attempt classification is inconclusive: neither the "
            "found-countermodel nor the not-found/source-map-ladder branch was "
            "selected."
        ),
        (
            "The attempt did not find a countermodel or no-go result, but it "
            "also did not establish that no countermodel exists."
        ),
        (
            "The sharper obstruction is missing specificity in the broader "
            "source/test instantiation and pinned weak-pairing semantics."
        ),
        (
            "The strict toy positive witness remains valid under its strict "
            "antecedents and is not refuted by the broader-family attempt."
        ),
    ]


def _validation_policy(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_attempt_result_review",
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
        "inherited_countermodel_attempt_validation_policy": attempt.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(attempt)
    scope_requirements = attempt.get("scope_refinement_requirements", [])
    scope_requirement_ids = {
        row.get("requirement_id") for row in scope_requirements
    }

    acceptance_criteria = {
        "consumes_expected_countermodel_attempt": (
            attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID
            and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
            and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME
            and attempt.get("result_classification")
            == EXPECTED_ATTEMPT_CLASSIFICATION
            and attempt.get("selected_next_target") == CONSUMED_TARGET
        ),
        "attempt_executed_and_accepted": (
            attempt.get("executed") is True
            and attempt.get("accepted") is True
            and attempt.get("countermodel_attempt_executed") is True
            and attempt.get("countermodel_attempt_result_review_pending") is True
        ),
        "inconclusive_classification_selected_only": (
            attempt.get("result_classification") == INCONCLUSIVE_CLASSIFICATION
            and attempt.get("selected_classification") == INCONCLUSIVE_CLASSIFICATION
            and attempt.get("result_classification_count") == 1
            and attempt.get("selected_classification_count") == 1
            and attempt.get("found_classification_not_selected") is True
            and attempt.get("not_found_classification_not_selected") is True
            and attempt.get("countermodel_found_pending_result_review") is False
            and attempt.get("countermodel_not_found_requires_source_map_ladder")
            is False
        ),
        "criteria_checked_without_selecting_countermodel_or_no_go": (
            attempt.get("countermodel_or_no_go_criteria_count") == 7
            and attempt.get("selected_countermodel_criterion_count") == 0
            and attempt.get("selected_no_go_criterion_count") == 0
            and all(
                row.get("selected_as_countermodel_or_no_go_result") == "no"
                for row in attempt.get("criteria_assessment", [])
            )
        ),
        "scope_refinement_requirements_identified": (
            attempt.get("scope_refinement_requirement_count") == 3
            and len(scope_requirements) == 3
            and scope_requirement_ids == EXPECTED_SCOPE_REQUIREMENT_IDS
            and attempt.get(
                "countermodel_scope_refinement_required_pending_result_review"
            )
            is True
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
        "review_selects_scope_refinement_packet_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
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
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION_RESULT_REVIEW"
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
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_CONSERVATION_"
            "OBSTRUCTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
            "obstruction_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_countermodel_attempt_id": EXPECTED_ATTEMPT_ID,
        "consumes_countermodel_attempt_pointer": _ptr(attempt_path),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "countermodel_attempt_result_review_accepted": accepted,
        "countermodel_attempt_consumed": accepted,
        "countermodel_attempt_executed": attempt.get("executed") is True,
        "countermodel_attempt_result_reviewed": accepted,
        "inconclusive_countermodel_attempt_accepted": accepted,
        "accepted_inconclusive_countermodel_attempt": accepted,
        "result_classification": INCONCLUSIVE_CLASSIFICATION,
        "selected_classification": INCONCLUSIVE_CLASSIFICATION,
        "found_classification": FOUND_CLASSIFICATION,
        "not_found_classification": NOT_FOUND_CLASSIFICATION,
        "found_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "countermodel_found_pending_result_review": False,
        "countermodel_not_found_requires_source_map_ladder": False,
        "countermodel_scope_refinement_required": accepted,
        "countermodel_scope_refinement_required_pending_result_review": (
            attempt.get("countermodel_scope_refinement_required_pending_result_review")
            is True
        ),
        "countermodel_scope_refinement_packet_authorized": accepted,
        "countermodel_scope_refinement_packet_authorized_only": accepted,
        "countermodel_scope_refinement_packet_prepared": False,
        "countermodel_scope_refinement_packet_executed": False,
        "scope_refinement_packet_preparation_pending": accepted,
        "scope_refinement_requirements": scope_requirements,
        "scope_refinement_requirement_count": len(scope_requirements),
        "selected_countermodel_criterion_count": 0,
        "selected_no_go_criterion_count": 0,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": attempt.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "countermodel_attempt_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "countermodel_scope_refinement_lane_retained_as_follow_on": True,
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
            "required for this routine bounded countermodel-attempt result-"
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
            "PREPARE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_"
            "FOR_WEAK_CONSERVATION_OBSTRUCTION_ONLY_NO_COUNTERMODEL_RESULT_"
            "CLAIM_NO_NO_GO_RESULT_CLAIM_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_"
            "SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_"
            "PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the inconclusive bounded "
            "countermodel attempt and authorizes only a countermodel scope-"
            "refinement packet for the weak-conservation obstruction. It does "
            "not claim a countermodel result, does not claim a no-go result, "
            "does not claim a not-found result, does not refute the accepted "
            "strict toy witness, preserves no source admissibility, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no broad "
            "QFT-GR conservation, no QFT-GR closure, no empirical validation, "
            "no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal model countermodel-attempt result "
            "review for the weak-conservation obstruction."
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
    payload = write_qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review(
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
                "accepted": payload["accepted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
