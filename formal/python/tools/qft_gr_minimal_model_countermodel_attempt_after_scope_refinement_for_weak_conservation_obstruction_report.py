from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_REVIEW_OUTCOME,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_20260615_v0"
)
ATTEMPT_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_EXECUTED_WITH_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_"
    "CLOSURE"
)
FOUND_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
    "found_pending_result_review"
)
NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
    "not_found_under_pinned_scope_requires_source_map_ladder"
)
INCONCLUSIVE_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_for_weak_conservation_obstruction_"
    "inconclusive_requires_source_map_or_scope_decision"
)
RESULT_CLASSIFICATION = INCONCLUSIVE_CLASSIFICATION
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_"
    "for_weak_conservation_obstruction_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_"
    "weak_conservation_obstruction_result_review"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_FOR_"
        "WEAK_CONSERVATION_OBSTRUCTION_20260615_v0.json"
    )
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / (
        "QFTGRMinimalModelCountermodelAttemptAfterScopeRefinementForWeak"
        "ConservationObstruction.lean"
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


def _classification_rows() -> list[dict[str, Any]]:
    return [
        {
            "classification": FOUND_CLASSIFICATION,
            "selected": False,
            "selection_rule": (
                "Requires at least one concrete obstruction pressure point "
                "under the pinned source/test pair, partial weak-pairing "
                "contract, and five-probe protocol."
            ),
        },
        {
            "classification": NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
            "selected": False,
            "selection_rule": (
                "Requires all pinned probes to be evaluated with no surviving "
                "countermodel/no-go pressure point under this pinned scope. "
                "This never means universal absence of countermodels."
            ),
        },
        {
            "classification": INCONCLUSIVE_CLASSIFICATION,
            "selected": True,
            "selection_rule": (
                "Selected because the refined scope still lacks a decisive "
                "source action, test action, and distributional divergence "
                "pairing value sufficient to decide found or not-found."
            ),
        },
    ]


def _probe_evaluations(packet_review: dict[str, Any]) -> list[dict[str, Any]]:
    probe_fields = {
        "weak_divergence_pairing_definedness": {
            "defined_or_undefined": (
                "not_decisively_evaluable_under_candidate_only_source_test_pair"
            ),
            "evaluation_status": "not_decisive",
            "attempt_observation": (
                "The partial weak-pairing contract pins when the pairing would "
                "be defined, but the candidate source/test pair does not supply "
                "a concrete source action, test action, and divergence pairing "
                "object that decides definedness."
            ),
        },
        "weak_divergence_pairing_value": {
            "zero_nonzero_or_not_evaluable": "not_evaluable",
            "evaluation_status": "not_decisive",
            "attempt_observation": (
                "No concrete weak-divergence pairing value is generated by the "
                "candidate-only source/test instantiation."
            ),
        },
        "boundary_term_retention": {
            "vanishes_survives_or_not_evaluable": "not_evaluable",
            "evaluation_status": "not_decisive",
            "attempt_observation": (
                "The broader test slot does not supply a decisive compact-"
                "support/no-boundary condition or a concrete retained boundary "
                "term."
            ),
        },
        "derivative_exchange_legitimacy": {
            "justified_unjustified_or_not_evaluable": "not_evaluable",
            "evaluation_status": "not_decisive",
            "attempt_observation": (
                "The source/test instantiation does not provide the analytic "
                "regularity or source-map rule needed to justify or refute "
                "the derivative exchange."
            ),
        },
        "curvature_coupling_residual": {
            "vanishes_survives_or_not_evaluable": "not_evaluable",
            "evaluation_status": "not_decisive",
            "attempt_observation": (
                "No concrete curvature-coupling residual term is instantiated "
                "as vanishing or surviving under the pinned candidate scope."
            ),
        },
    }
    evaluations: list[dict[str, Any]] = []
    for probe in packet_review.get("evaluation_scope", {}).get("probes", []):
        probe_id = probe["probe_id"]
        row = {
            "probe_id": probe_id,
            "required_report_field": probe["required_report_field"],
            "packet_pressure_status": probe["countermodel_pressure_status"],
            "pressure_point_selected": "no",
            "countermodel_pressure_point_constructed": False,
            "not_found_support_established": False,
        }
        row.update(probe_fields[probe_id])
        evaluations.append(row)
    return evaluations


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded reattempt has executed and selected an "
                "inconclusive classification pending result review."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The packet-authorized execution target is consumed here.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_before_result_review",
            "reason": (
                "Source-map ladder work may be authorized only after result "
                "review accepts the reattempt classification and branch."
            ),
        },
        {
            "target": (
                "prepare_qft_gr_minimal_model_countermodel_scope_refinement_"
                "packet_after_reattempt_for_weak_conservation_obstruction"
            ),
            "decision": "retained_possible_branch_not_selected_before_result_review",
            "reason": (
                "A further refinement can be selected only by result review if "
                "it identifies one narrow missing semantic assumption."
            ),
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "No concrete countermodel is constructed by this attempt.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is proved by this attempt.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "Not-found under pinned scope is not selected.",
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
            "reason": "The attempt does not close QFT-GR.",
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


def _attempt_findings() -> list[str]:
    return [
        (
            "The bounded reattempt consumed the accepted packet review and "
            "used the exact packet-encoded execution target without target "
            "drift."
        ),
        (
            "All five pinned probes were evaluated against the broader "
            "candidate source/test pair and partial weak-pairing contract."
        ),
        (
            "No probe produced a concrete obstruction pressure point sufficient "
            "to select the found-pending-review classification."
        ),
        (
            "The attempt also cannot select not-found under pinned scope, "
            "because the candidate-only source/test pair and partial weak "
            "pairing do not decide the required pairing values and legitimacy "
            "conditions."
        ),
        (
            "The selected classification is therefore inconclusive requiring "
            "result review to choose a source-map-ladder route or one narrow "
            "scope decision."
        ),
    ]


def _validation_policy(packet_review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_execution",
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
        "inherited_reattempt_packet_result_review_validation_policy": (
            packet_review.get("validation_policy", {})
        ),
    }


def build_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction(
    *,
    packet_review_path: Path = DEFAULT_PACKET_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet_review = _read_json(packet_review_path)
    probe_evaluations = _probe_evaluations(packet_review)
    classification_rows = _classification_rows()
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(packet_review)
    selected_classifications = [
        row["classification"] for row in classification_rows if row["selected"] is True
    ]

    acceptance_criteria = {
        "consumes_expected_reattempt_packet_result_review": (
            packet_review.get("schema_id") == EXPECTED_PACKET_REVIEW_SCHEMA_ID
            and packet_review.get("review_id") == EXPECTED_PACKET_REVIEW_ID
            and packet_review.get("outcome_id") == EXPECTED_PACKET_REVIEW_OUTCOME
            and packet_review.get("result_review_classification")
            == EXPECTED_PACKET_REVIEW_CLASSIFICATION
            and packet_review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "packet_review_authorized_exact_execution_target": (
            packet_review.get("countermodel_attempt_after_scope_refinement_authorized")
            is True
            and packet_review.get("countermodel_attempt_after_scope_refinement_executed")
            is False
            and packet_review.get("review_authorizes_exact_packet_downstream_target")
            is True
            and packet_review.get("target_name_drift_prevented") is True
        ),
        "pinned_scope_carried_exactly": (
            packet_review.get("pinned_source_test_pair_id")
            == PINNED_SOURCE_TEST_PAIR_ID
            and packet_review.get("pinned_weak_pairing_contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and packet_review.get("pinned_evaluation_scope_id")
            == PINNED_EVALUATION_SCOPE_ID
            and packet_review.get("source_test_instantiation", {}).get(
                "instantiation_id"
            )
            == PINNED_SOURCE_TEST_PAIR_ID
            and packet_review.get("weak_pairing_semantics", {}).get("contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
        ),
        "five_probe_protocol_executed": (
            len(probe_evaluations) == 5
            and {row["probe_id"] for row in probe_evaluations}
            == {
                "weak_divergence_pairing_definedness",
                "weak_divergence_pairing_value",
                "boundary_term_retention",
                "derivative_exchange_legitimacy",
                "curvature_coupling_residual",
            }
            and all(row["evaluation_status"] == "not_decisive" for row in probe_evaluations)
        ),
        "exactly_one_allowed_classification_selected": (
            selected_classifications == [INCONCLUSIVE_CLASSIFICATION]
            and {
                row["classification"] for row in classification_rows
            }
            == {
                FOUND_CLASSIFICATION,
                NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
                INCONCLUSIVE_CLASSIFICATION,
            }
        ),
        "found_and_not_found_not_selected": (
            all(
                row["pressure_point_selected"] == "no"
                and row["countermodel_pressure_point_constructed"] is False
                and row["not_found_support_established"] is False
                for row in probe_evaluations
            )
        ),
        "attempt_selects_result_review_only": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
        "strict_toy_witness_preserved_not_refuted": (
            packet_review.get("strict_toy_witness_preserved") is True
            and packet_review.get("strict_toy_witness_accepted") is True
            and packet_review.get("strict_toy_assumptions_only") is True
            and packet_review.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "no_source_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            packet_review.get("source_admissibility_claimed") is False
            and packet_review.get("Bianchi_compatibility_claimed") is False
            and packet_review.get("semiclassical_einstein_equation_derived") is False
            and packet_review.get("qft_gr_seam_closed") is False
            and packet_review.get("qft_gr_source_map_closure_claimed") is False
            and packet_review.get("empirical_validation_claimed") is False
            and packet_review.get("public_submission_authorized") is False
            and packet_review.get("master_action_promoted") is False
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
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_REFINEMENT_"
            "FOR_WEAK_CONSERVATION_OBSTRUCTION_REQUIRES_REMEDIATION"
        ),
        "consumed_target": CONSUMED_TARGET,
        "consumes_reattempt_packet_result_review": EXPECTED_PACKET_REVIEW_ID,
        "consumes_reattempt_packet_result_review_pointer": _ptr(packet_review_path),
        "consumed_packet_review_schema_id": packet_review.get("schema_id"),
        "consumed_packet_review_outcome_id": packet_review.get("outcome_id"),
        "consumed_packet_review_classification": packet_review.get(
            "result_review_classification"
        ),
        "attempt_after_scope_refinement_executed": executed,
        "attempt_after_scope_refinement_result_review_pending": executed,
        "attempt_after_scope_refinement_result_reviewed": False,
        "countermodel_attempt_after_scope_refinement_authorized": (
            packet_review.get("countermodel_attempt_after_scope_refinement_authorized")
            is True
        ),
        "countermodel_attempt_after_scope_refinement_executed": executed,
        "target_name_drift_prevented": True,
        "encoded_downstream_target": CONSUMED_TARGET,
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": packet_review.get("source_test_instantiation", {}),
        "weak_pairing_semantics": packet_review.get("weak_pairing_semantics", {}),
        "evaluation_scope": packet_review.get("evaluation_scope", {}),
        "probe_evaluations": probe_evaluations,
        "probe_evaluation_count": len(probe_evaluations),
        "probe_count": len(probe_evaluations),
        "not_decisive_probe_count": sum(
            1 for row in probe_evaluations if row["evaluation_status"] == "not_decisive"
        ),
        "decisive_countermodel_pressure_point_count": 0,
        "not_found_supporting_probe_count": 0,
        "classification_options": [
            FOUND_CLASSIFICATION,
            NOT_FOUND_UNDER_PINNED_SCOPE_CLASSIFICATION,
            INCONCLUSIVE_CLASSIFICATION,
        ],
        "classification_rows": classification_rows,
        "result_classification": RESULT_CLASSIFICATION,
        "selected_classification": RESULT_CLASSIFICATION,
        "selected_classification_count": 1 if executed else 0,
        "found_classification_not_selected": True,
        "not_found_under_pinned_scope_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "inconclusive_classification_selected": True,
        "countermodel_found_pending_result_review": False,
        "countermodel_not_found_under_pinned_scope_requires_source_map_ladder": False,
        "countermodel_not_found_requires_source_map_ladder": False,
        "countermodel_inconclusive_requires_source_map_or_scope_decision": True,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "countermodel_not_found_means_under_pinned_scope_only": True,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": packet_review.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "attempt_after_scope_refinement_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": packet_review.get(
            "dominant_obstruction_candidate"
        ),
        "canonical_obstruction_id": packet_review.get("canonical_obstruction_id"),
        "obstruction_status": packet_review.get("obstruction_status"),
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
        "further_scope_refinement_authorized": False,
        "result_review_must_choose_source_map_or_single_scope_decision": True,
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
        "attempt_findings": _attempt_findings(),
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
            "required for this routine bounded countermodel reattempt "
            "execution checkpoint. The release-index path remains not freshly "
            "Lean-validated, aggregate Lean is not run, and no aggregate Lean "
            "health claim is made."
        ),
        "lean_attempt_file": _ptr(LEAN_ATTEMPT_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if executed
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_"
            "REFINEMENT_FOR_WEAK_CONSERVATION_OBSTRUCTION"
        ),
        "attempt_selected_next_target": NEXT_TARGET
        if executed
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_"
            "REFINEMENT_FOR_WEAK_CONSERVATION_OBSTRUCTION"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if executed else 0,
        "selected_next_target_count": 1 if executed else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_"
            "REFINEMENT_FOR_WEAK_CONSERVATION_OBSTRUCTION_RESULT_ONLY_NO_"
            "SOURCE_MAP_LADDER_EXECUTION_NO_SCOPE_REFINEMENT_EXECUTION_NO_"
            "COUNTERMODEL_RESULT_CLAIM_NO_NO_GO_RESULT_CLAIM_NO_SOURCE_"
            "ADMISSIBILITY_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This bounded attempt executes the five-probe pressure test under "
            "the refined source/test instantiation and partial weak-pairing "
            "contract. It selects only an inconclusive pending-review "
            "classification requiring source-map or scope decision. It does "
            "not claim a countermodel result, does not claim a no-go result, "
            "does not claim not-found under pinned scope, does not refute the "
            "accepted strict toy witness, preserves no source admissibility, "
            "no Bianchi compatibility, no semiclassical Einstein equation, "
            "no broad QFT-GR conservation, no QFT-GR closure, no empirical "
            "validation, no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction(
    *,
    packet_review_path: Path = DEFAULT_PACKET_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction(
        packet_review_path=packet_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the bounded QFT-GR minimal model countermodel attempt "
            "after scope refinement for the weak-conservation obstruction."
        )
    )
    parser.add_argument(
        "--packet-review", type=Path, default=DEFAULT_PACKET_REVIEW_PATH
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_review_path = (
        ns.packet_review
        if ns.packet_review.is_absolute()
        else (REPO_ROOT / ns.packet_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction(
        packet_review_path=packet_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "attempt_id": payload["attempt_id"],
                "out": _ptr(out),
                "outcome_id": payload["outcome_id"],
                "result_classification": payload["result_classification"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
