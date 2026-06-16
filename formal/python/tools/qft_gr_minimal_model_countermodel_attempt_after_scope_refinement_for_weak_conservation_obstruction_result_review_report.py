from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_ATTEMPT_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_20260616_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_ACCEPTS_INCONCLUSIVE_REATTEMPT_"
    "AND_AUTHORIZES_SOURCE_MAP_OR_SCOPE_DECISION_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_"
    "conservation_obstruction_result_review_accepts_inconclusive_reattempt_"
    "and_authorizes_source_map_or_scope_decision_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "prepare_qft_gr_source_map_or_countermodel_scope_decision_packet"
NEXT_TARGET_KIND = "qft_gr_source_map_or_countermodel_scope_decision_packet_preparation"
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source"
)
COUNTERMODEL_SCOPE_DECISION_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_scope_refinement_packet_after_"
    "reattempt_for_weak_conservation_obstruction"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_"
        "WEAK_CONSERVATION_OBSTRUCTION_RESULT_REVIEW_20260616_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalModelCountermodelAttemptAfterScopeRefinementForWeak"
        "ConservationObstructionResultReview.lean"
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
                "The reattempt result is accepted as inconclusive, so the "
                "only authorized next action is a source-map-or-scope decision "
                "packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The reattempt result-review target is consumed here.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_branch_candidate_not_selected_until_decision_packet",
            "reason": (
                "The decision packet may select this by default unless it "
                "identifies exactly one narrow scope condition."
            ),
        },
        {
            "target": COUNTERMODEL_SCOPE_DECISION_TARGET,
            "decision": "retained_branch_candidate_not_selected_until_decision_packet",
            "reason": (
                "The decision packet may select this only if one narrow "
                "semantic condition can directly decide a pinned probe."
            ),
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "No concrete countermodel is constructed or accepted.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is proved or accepted.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "Not-found under pinned scope is not accepted.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The source remains candidate-only and not admissible.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened.",
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
            "reason": "The review does not close QFT-GR.",
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
            "The executed reattempt consumed the accepted reattempt-packet "
            "result review and preserved the exact packet-encoded target."
        ),
        (
            "All five pinned probes were evaluated, but each remained "
            "non-decisive under the candidate-only source/test pair and "
            "partial weak-pairing contract."
        ),
        (
            "The review accepts the inconclusive classification and rejects "
            "found, no-go, and not-found-under-pinned-scope result claims."
        ),
        (
            "The next checkpoint must decide between a source-map ladder route "
            "and exactly one narrow countermodel scope condition."
        ),
        (
            "The strict toy weak-conservation witness remains accepted only "
            "under its strict antecedents."
        ),
    ]


def _validation_policy(attempt: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_result_review",
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
        "inherited_attempt_validation_policy": attempt.get("validation_policy", {}),
    }


def build_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(attempt)

    acceptance_criteria = {
        "consumes_expected_attempt": (
            attempt.get("schema_id") == EXPECTED_ATTEMPT_SCHEMA_ID
            and attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID
            and attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME
            and attempt.get("result_classification") == EXPECTED_ATTEMPT_CLASSIFICATION
            and attempt.get("selected_next_target") == CONSUMED_TARGET
        ),
        "attempt_executed_pending_review": (
            attempt.get("accepted") is True
            and attempt.get("attempt_after_scope_refinement_executed") is True
            and attempt.get("attempt_after_scope_refinement_result_review_pending")
            is True
            and attempt.get("attempt_after_scope_refinement_result_reviewed") is False
        ),
        "accepts_inconclusive_classification_only": (
            attempt.get("selected_classification") == INCONCLUSIVE_CLASSIFICATION
            and attempt.get("selected_classification_count") == 1
            and attempt.get("countermodel_inconclusive_requires_source_map_or_scope_decision")
            is True
            and attempt.get("countermodel_found_pending_result_review") is False
            and attempt.get("countermodel_not_found_under_pinned_scope_requires_source_map_ladder")
            is False
        ),
        "all_probes_non_decisive": (
            attempt.get("probe_evaluation_count") == 5
            and attempt.get("not_decisive_probe_count") == 5
            and attempt.get("decisive_countermodel_pressure_point_count") == 0
            and attempt.get("not_found_supporting_probe_count") == 0
            and all(
                row.get("evaluation_status") == "not_decisive"
                and row.get("countermodel_pressure_point_constructed") is False
                and row.get("not_found_support_established") is False
                for row in attempt.get("probe_evaluations", [])
            )
        ),
        "pinned_scope_preserved": (
            attempt.get("pinned_source_test_pair_id") == PINNED_SOURCE_TEST_PAIR_ID
            and attempt.get("pinned_weak_pairing_contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and attempt.get("pinned_evaluation_scope_id") == PINNED_EVALUATION_SCOPE_ID
        ),
        "decision_packet_selected_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "decision_packet_has_two_branch_candidates": {
            row["target"]
            for row in candidate_next_targets
            if row["decision"]
            == "retained_branch_candidate_not_selected_until_decision_packet"
        }
        == {SOURCE_MAP_LADDER_TARGET, COUNTERMODEL_SCOPE_DECISION_TARGET},
        "branch_default_and_loop_guard_recorded": (
            SOURCE_MAP_LADDER_TARGET
            == "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source"
            and COUNTERMODEL_SCOPE_DECISION_TARGET
            == "prepare_qft_gr_minimal_model_countermodel_scope_refinement_packet_after_reattempt_for_weak_conservation_obstruction"
        ),
        "strict_toy_witness_preserved_not_refuted": (
            attempt.get("strict_toy_witness_preserved") is True
            and attempt.get("strict_toy_witness_accepted") is True
            and attempt.get("strict_toy_assumptions_only") is True
            and attempt.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "no_countermodel_no_go_not_found_or_source_claim": (
            attempt.get("countermodel_result_claimed") is False
            and attempt.get("countermodel_exists_claimed") is False
            and attempt.get("no_go_result_claimed") is False
            and attempt.get("not_found_result_claimed") is False
            and attempt.get("source_admissibility_claimed") is False
        ),
        "no_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            attempt.get("Bianchi_compatibility_claimed") is False
            and attempt.get("semiclassical_einstein_equation_derived") is False
            and attempt.get("qft_gr_seam_closed") is False
            and attempt.get("qft_gr_source_map_closure_claimed") is False
            and attempt.get("empirical_validation_claimed") is False
            and attempt.get("public_submission_authorized") is False
            and attempt.get("master_action_promoted") is False
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
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_"
            "REFINEMENT_FOR_WEAK_CONSERVATION_OBSTRUCTION_RESULT_REVIEW"
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
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_"
            "FOR_WEAK_CONSERVATION_OBSTRUCTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_"
            "for_weak_conservation_obstruction_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_attempt_id": EXPECTED_ATTEMPT_ID,
        "consumes_attempt_pointer": _ptr(attempt_path),
        "consumed_attempt_schema_id": attempt.get("schema_id"),
        "consumed_attempt_outcome_id": attempt.get("outcome_id"),
        "consumed_attempt_classification": attempt.get("result_classification"),
        "attempt_after_scope_refinement_result_review_accepted": accepted,
        "attempt_after_scope_refinement_result_reviewed": accepted,
        "attempt_after_scope_refinement_result_review_pending": False,
        "attempt_after_scope_refinement_executed": (
            attempt.get("attempt_after_scope_refinement_executed") is True
        ),
        "accepted_inconclusive_reattempt": accepted,
        "accepted_result_classification": INCONCLUSIVE_CLASSIFICATION,
        "found_classification_not_selected": True,
        "not_found_under_pinned_scope_classification_not_selected": True,
        "inconclusive_classification_accepted": accepted,
        "countermodel_found_pending_result_review": False,
        "countermodel_not_found_under_pinned_scope_requires_source_map_ladder": False,
        "countermodel_inconclusive_requires_source_map_or_scope_decision": accepted,
        "probe_evaluation_count": attempt.get("probe_evaluation_count"),
        "not_decisive_probe_count": attempt.get("not_decisive_probe_count"),
        "decisive_countermodel_pressure_point_count": attempt.get(
            "decisive_countermodel_pressure_point_count"
        ),
        "not_found_supporting_probe_count": attempt.get(
            "not_found_supporting_probe_count"
        ),
        "probe_evaluations": attempt.get("probe_evaluations", []),
        "classification_options": [
            FOUND_CLASSIFICATION,
            NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
            INCONCLUSIVE_CLASSIFICATION,
        ],
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": attempt.get("source_test_instantiation", {}),
        "weak_pairing_semantics": attempt.get("weak_pairing_semantics", {}),
        "evaluation_scope": attempt.get("evaluation_scope", {}),
        "dominant_obstruction_candidate": attempt.get("dominant_obstruction_candidate"),
        "canonical_obstruction_id": attempt.get("canonical_obstruction_id"),
        "obstruction_status": "accepted_inconclusive_requires_decision_packet",
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "source_map_or_scope_decision_packet_authorized": accepted,
        "source_map_or_scope_decision_packet_prepared": False,
        "source_map_ladder_packet_authorized": False,
        "further_scope_refinement_authorized": False,
        "decision_packet_branch_targets": [
            SOURCE_MAP_LADDER_TARGET,
            COUNTERMODEL_SCOPE_DECISION_TARGET,
        ],
        "decision_packet_default_branch": SOURCE_MAP_LADDER_TARGET,
        "decision_packet_scope_branch": COUNTERMODEL_SCOPE_DECISION_TARGET,
        "source_map_ladder_default_unless_single_scope_condition": True,
        "single_narrow_scope_condition_required_for_scope_refinement": True,
        "only_one_narrow_scope_refinement_cycle_allowed": True,
        "source_map_forced_after_one_scope_refinement_cycle": True,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": attempt.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "result_review_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
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
            "required for this routine bounded countermodel reattempt result-"
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
            "PREPARE_QFT_GR_SOURCE_MAP_OR_COUNTERMODEL_SCOPE_DECISION_PACKET_"
            "ONLY_NO_SOURCE_MAP_LADDER_EXECUTION_NO_SCOPE_REFINEMENT_EXECUTION_"
            "NO_COUNTERMODEL_RESULT_CLAIM_NO_NO_GO_RESULT_CLAIM_NO_SOURCE_"
            "ADMISSIBILITY_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the inconclusive bounded "
            "countermodel reattempt after scope refinement and authorizes only "
            "a source-map-or-countermodel-scope decision packet. It does not "
            "claim a countermodel result, does not claim a no-go result, does "
            "not claim not-found under pinned scope, does not refute the "
            "accepted strict toy witness, preserves no source admissibility, "
            "no Bianchi compatibility, no semiclassical Einstein equation, "
            "no broad QFT-GR conservation, no QFT-GR closure, no empirical "
            "validation, no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the bounded QFT-GR minimal model countermodel attempt "
            "after scope refinement result review for the weak-conservation "
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
    payload = write_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(out),
                "outcome_id": payload["outcome_id"],
                "result_review_classification": payload[
                    "result_review_classification"
                ],
                "review_id": payload["review_id"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
