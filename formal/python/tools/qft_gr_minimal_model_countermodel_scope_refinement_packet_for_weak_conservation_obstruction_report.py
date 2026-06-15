from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_obstruction_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    EXPECTED_SCOPE_REQUIREMENT_IDS,
    INCONCLUSIVE_CLASSIFICATION,
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
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_20260615_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_PREPARED_WITH_NO_COUNTERMODEL_RESULT_OR_QFT_GR_"
    "CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_"
    "conservation_obstruction_prepared_with_no_countermodel_result_or_qft_gr_"
    "closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_"
    "weak_conservation_obstruction_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_"
    "conservation_obstruction_result_review"
)
PINNED_SOURCE_TEST_PAIR_ID = (
    "broader_candidate_source_allowed_test_pair_for_weak_conservation_"
    "countermodel_v0"
)
PINNED_WEAK_PAIRING_CONTRACT_ID = (
    "partial_weak_pairing_contract_for_broader_countermodel_scope_v0"
)
PINNED_EVALUATION_SCOPE_ID = (
    "broader_weak_divergence_boundary_and_curvature_evaluation_scope_v0"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_FOR_WEAK_"
        "CONSERVATION_OBSTRUCTION_20260615_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelScopeRefinementPacketForWeakConservationObstruction.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _scope_refinement_rows() -> list[dict[str, str]]:
    return [
        {
            "requirement_id": "concrete_broader_source_test_pair",
            "refinement_id": PINNED_SOURCE_TEST_PAIR_ID,
            "selected_source_candidate": (
                "broader_stress_energy_like_distribution_candidate_not_source_"
                "admissible_v0"
            ),
            "selected_test_object": (
                "broader_allowed_weak_test_vector_or_probe_not_bianchi_"
                "witness_v0"
            ),
            "pinned_semantics": (
                "A later attempt must instantiate this source/test slot before "
                "evaluating the prepared countermodel/no-go criteria."
            ),
            "claim_ceiling": (
                "source_test_instantiation_scope_only_no_source_admissibility_"
                "and_no_countermodel_result"
            ),
        },
        {
            "requirement_id": "weak_pairing_totality_or_partiality_contract",
            "refinement_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
            "selected_pairing_semantics": (
                "partial_weak_pairing_defined_only_when_source_action_test_"
                "action_and_distributional_divergence_pairing_are_defined"
            ),
            "undefined_pairing_status": (
                "undefined_pairing_is_countermodel_pressure_point_not_source_"
                "admissibility_claim"
            ),
            "pinned_semantics": (
                "A future attempt may classify an undefined required weak "
                "pairing as obstruction evidence, but not as a source-"
                "admissibility result."
            ),
            "claim_ceiling": (
                "weak_pairing_semantics_scope_only_no_no_go_or_not_found_result"
            ),
        },
        {
            "requirement_id": "broader_divergence_or_boundary_evaluation_scope",
            "refinement_id": PINNED_EVALUATION_SCOPE_ID,
            "selected_evaluation_scope": (
                "weak_divergence_pairing_boundary_term_derivative_exchange_"
                "and_curvature_coupling_residual_probes"
            ),
            "boundary_semantics": (
                "boundary_terms_are_retained_as_probe_outputs_not_discarded_by_"
                "compact_support_unless_the_selected_test_object_supplies_that_"
                "condition"
            ),
            "pinned_semantics": (
                "A future attempt must report whether each broader divergence, "
                "boundary, derivative-exchange, or curvature-coupling probe is "
                "defined and whether it vanishes."
            ),
            "claim_ceiling": (
                "evaluation_scope_only_no_conservation_proof_or_qft_gr_closure"
            ),
        },
    ]


def _future_attempt_decision_criteria() -> list[dict[str, str]]:
    return [
        {
            "classification": (
                "qft_gr_minimal_model_countermodel_for_weak_conservation_"
                "obstruction_found_pending_result_review"
            ),
            "decision_rule": (
                "Select only if the pinned broader source/test pair and "
                "partial-pairing semantics exhibit one prepared obstruction "
                "criterion with a concrete defined or undefined evaluation "
                "status."
            ),
        },
        {
            "classification": (
                "qft_gr_minimal_model_countermodel_for_weak_conservation_"
                "obstruction_not_found_requires_source_map_ladder"
            ),
            "decision_rule": (
                "Select only if every pinned criterion is evaluated under the "
                "refined semantics and no countermodel/no-go pressure point "
                "survives."
            ),
        },
        {
            "classification": INCONCLUSIVE_CLASSIFICATION,
            "decision_rule": (
                "Select if the pinned refinement still lacks enough semantics "
                "to decide found or not-found status."
            ),
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The packet is preparation only; result review must accept the "
                "pinned scope before any bounded countermodel attempt can be "
                "reauthorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The scope-refinement packet preparation target is consumed here.",
        },
        {
            "target": (
                "execute_qft_gr_minimal_model_countermodel_attempt_for_weak_"
                "conservation_obstruction_after_scope_refinement"
            ),
            "decision": "not_authorized_until_packet_result_review",
            "reason": "The packet does not execute or authorize a new countermodel attempt.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_packet",
            "reason": "Source-map ladder work remains downstream of a reviewed attempt result.",
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "No countermodel is found or claimed by packet preparation.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is found or claimed by packet preparation.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The pinned source remains a candidate only.",
        },
        {
            "target": "claim_broad_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The strict toy witness is not broadened by this packet.",
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
            "reason": "Scope refinement packet preparation does not close QFT-GR.",
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


def _validation_policy(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_scope_refinement_packet_preparation",
        "routine_packet_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_countermodel_attempt_result_review_validation_policy": review.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    rows = _scope_refinement_rows()
    row_ids = {row["requirement_id"] for row in rows}
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(review)

    acceptance_criteria = {
        "consumes_expected_result_review": (
            review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "result_review_authorized_packet_only": (
            review.get("accepted") is True
            and review.get("countermodel_scope_refinement_packet_authorized") is True
            and review.get("countermodel_scope_refinement_packet_authorized_only")
            is True
            and review.get("countermodel_scope_refinement_packet_prepared") is False
        ),
        "scope_requirements_pinned_exactly": (
            len(rows) == 3
            and row_ids == EXPECTED_SCOPE_REQUIREMENT_IDS
            and review.get("scope_refinement_requirement_count") == 3
        ),
        "source_test_pair_pinned_without_source_admissibility": (
            rows[0]["refinement_id"] == PINNED_SOURCE_TEST_PAIR_ID
            and "not_source_admissible" in rows[0]["selected_source_candidate"]
            and review.get("source_admissibility_claimed") is False
        ),
        "weak_pairing_contract_pinned_as_partial": (
            rows[1]["refinement_id"] == PINNED_WEAK_PAIRING_CONTRACT_ID
            and rows[1]["selected_pairing_semantics"].startswith(
                "partial_weak_pairing"
            )
        ),
        "evaluation_scope_pinned_without_conservation_proof": (
            rows[2]["refinement_id"] == PINNED_EVALUATION_SCOPE_ID
            and "weak_divergence_pairing" in rows[2]["selected_evaluation_scope"]
            and review.get("conservation_proved") is False
        ),
        "decision_criteria_retain_three_attempt_classifications": (
            len(_future_attempt_decision_criteria()) == 3
        ),
        "strict_toy_witness_preserved_not_refuted": (
            review.get("strict_toy_witness_preserved") is True
            and review.get("strict_toy_witness_accepted") is True
            and review.get("strict_toy_assumptions_only") is True
            and review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "obstruction_candidate_carried_unresolved": (
            review.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and review.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and review.get("obstruction_status") == OBSTRUCTION_STATUS
            and review.get("dominant_obstruction_resolved") is False
            and review.get("mathematical_resolution_claimed") is False
        ),
        "packet_selects_result_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "no_countermodel_no_go_or_attempt_execution": (
            review.get("countermodel_result_claimed") is False
            and review.get("countermodel_exists_claimed") is False
            and review.get("countermodel_achieved") is False
            and review.get("no_go_result_claimed") is False
            and review.get("not_found_result_claimed") is False
        ),
        "no_source_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            review.get("source_admissibility_claimed") is False
            and review.get("Bianchi_compatibility_claimed") is False
            and review.get("semiclassical_einstein_equation_derived") is False
            and review.get("qft_gr_seam_closed") is False
            and review.get("qft_gr_source_map_closure_claimed") is False
            and review.get("empirical_validation_claimed") is False
            and review.get("public_submission_authorized") is False
            and review.get("master_action_promoted") is False
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
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_decision": "prepared" if prepared else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if prepared
        else (
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION_REQUIRES_REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_countermodel_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_countermodel_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": review.get("schema_id"),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "countermodel_attempt_result_review_accepted": review.get("accepted") is True,
        "countermodel_attempt_result_classification": INCONCLUSIVE_CLASSIFICATION,
        "countermodel_attempt_result_inconclusive": True,
        "countermodel_scope_refinement_packet_prepared": prepared,
        "countermodel_scope_refinement_packet_preparation_only": True,
        "countermodel_scope_refinement_packet_authorized": True,
        "countermodel_scope_refinement_packet_authorized_only": True,
        "countermodel_scope_refinement_packet_result_review_pending": prepared,
        "countermodel_scope_refinement_packet_result_reviewed": False,
        "countermodel_attempt_authorized_by_packet": False,
        "countermodel_attempt_executed_by_packet": False,
        "countermodel_attempt_reexecuted": False,
        "countermodel_search_space_refined": prepared,
        "source_test_instantiation_pinned": prepared,
        "weak_pairing_semantics_pinned": prepared,
        "broader_divergence_boundary_evaluation_scope_pinned": prepared,
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "scope_refinement_rows": rows,
        "scope_refinement_row_count": len(rows),
        "future_attempt_decision_criteria": _future_attempt_decision_criteria(),
        "future_attempt_decision_criteria_count": 3,
        "selected_countermodel_criterion_count": 0,
        "selected_no_go_criterion_count": 0,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": review.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "countermodel_packet_is_not_strict_toy_witness_refutation": True,
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
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_packet_current_target_registry_gate": "required_for_checkpoint",
            "adjacent_qft_gr_nonclaim_gates": "required_bounded_subset",
            "targeted_lean_packet_frontier_import_checks": "required_for_checkpoint",
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
            "required for this routine bounded scope-refinement packet "
            "checkpoint. The release-index path remains not freshly Lean-"
            "validated, aggregate Lean is not run, and no aggregate Lean health "
            "claim is made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_"
            "PACKET_FOR_WEAK_CONSERVATION_OBSTRUCTION"
        ),
        "packet_selected_next_target": NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_"
            "PACKET_FOR_WEAK_CONSERVATION_OBSTRUCTION"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if prepared else 0,
        "selected_next_target_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_SCOPE_REFINEMENT_PACKET_"
            "FOR_WEAK_CONSERVATION_OBSTRUCTION_RESULT_ONLY_NO_COUNTERMODEL_"
            "ATTEMPT_EXECUTION_NO_COUNTERMODEL_RESULT_CLAIM_NO_NO_GO_RESULT_"
            "CLAIM_NO_SOURCE_ADMISSIBILITY_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet refines only the countermodel search space by pinning "
            "a broader candidate source/test instantiation, a partial weak-"
            "pairing contract, and a broader divergence/boundary evaluation "
            "scope for later review. It does not execute a countermodel "
            "attempt, does not claim a countermodel result, does not claim a "
            "no-go result, does not claim source admissibility, does not "
            "claim Bianchi compatibility, does not derive a semiclassical "
            "Einstein equation, does not claim broad QFT-GR conservation, "
            "does not close QFT-GR, does not validate empirically, does not "
            "authorize public submission, and does not promote the master "
            "action. Boundary shorthand: no countermodel result, no no-go "
            "result, no source admissibility, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no broad QFT-GR conservation, "
            "no QFT-GR closure, no empirical validation, no public "
            "submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal model countermodel scope-refinement "
            "packet for the weak-conservation obstruction."
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
    payload = write_qft_gr_minimal_model_countermodel_scope_refinement_packet_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "selected_next_target": payload["selected_next_target"],
                "prepared": payload["prepared"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
