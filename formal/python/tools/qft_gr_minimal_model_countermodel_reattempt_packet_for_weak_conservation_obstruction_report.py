from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_scope_refinement_attempt_for_weak_conservation_obstruction_result_review_report import (
    CANONICAL_OBSTRUCTION_ID,
    COUNTERMODEL_REATTEMPT_TARGET,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    NOT_FOUND_CLASSIFICATION,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_20260615_v0"
)
PACKET_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_PREPARED_WITH_NO_COUNTERMODEL_RESULT_OR_QFT_GR_"
    "CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_"
    "obstruction_prepared_with_no_countermodel_result_or_qft_gr_closure"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = (
    "review_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_"
    "conservation_obstruction_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_"
    "obstruction_result_review"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
        "CONSERVATION_OBSTRUCTION_20260615_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelReattemptPacketForWeakConservationObstruction.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _reattempt_probe_plan(review: dict[str, Any]) -> list[dict[str, str]]:
    probes = review.get("evaluation_scope", {}).get("probes", [])
    return [
        {
            "probe_id": probe["probe_id"],
            "required_report_field": probe["required_report_field"],
            "countermodel_pressure_status": probe["countermodel_pressure_status"],
            "packet_instruction": (
                "A later bounded reattempt must instantiate this probe against "
                "the pinned source/test pair and partial weak-pairing contract "
                "before selecting found, not-found, or inconclusive status."
            ),
            "selected_now": "no",
        }
        for probe in probes
    ]


def _allowed_reattempt_classifications() -> list[dict[str, str]]:
    return [
        {
            "classification": FOUND_CLASSIFICATION,
            "selected_now": "no",
            "packet_rule": (
                "May be selected only by a later bounded reattempt if the "
                "pinned source/test pair and partial weak-pairing semantics "
                "produce a concrete obstruction pressure point."
            ),
        },
        {
            "classification": NOT_FOUND_CLASSIFICATION,
            "selected_now": "no",
            "packet_rule": (
                "May be selected only by a later bounded reattempt if all "
                "pinned probes are evaluated and no countermodel/no-go pressure "
                "point survives under the refined scope."
            ),
        },
        {
            "classification": INCONCLUSIVE_CLASSIFICATION,
            "selected_now": "no",
            "packet_rule": (
                "May be selected only by a later bounded reattempt if the "
                "refined scope still lacks enough semantics to decide found or "
                "not-found status."
            ),
        },
    ]


def _reattempt_decision_protocol(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "protocol_id": (
            "qft_gr_minimal_model_countermodel_reattempt_decision_protocol_"
            "for_refined_weak_conservation_scope_v0"
        ),
        "source_test_instantiation_id": review.get("pinned_source_test_pair_id"),
        "weak_pairing_contract_id": review.get("pinned_weak_pairing_contract_id"),
        "evaluation_scope_id": review.get("pinned_evaluation_scope_id"),
        "probe_count": len(_reattempt_probe_plan(review)),
        "found_requires": (
            "at_least_one_concrete_obstruction_pressure_point_under_pinned_"
            "source_test_pair_partial_pairing_and_probe_protocol"
        ),
        "not_found_requires": (
            "all_pinned_probes_evaluated_with_no_surviving_pressure_point_"
            "under_refined_scope"
        ),
        "inconclusive_requires": (
            "remaining_semantic_gap_prevents_found_or_not_found_decision_"
            "despite_refined_scope"
        ),
        "review_required_before_execution": "yes",
    }


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The reattempt packet is preparation only, so the next action "
                "is bounded packet result review."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The reattempt packet preparation target is consumed here.",
        },
        {
            "target": COUNTERMODEL_REATTEMPT_TARGET,
            "decision": "not_authorized_until_reattempt_packet_result_review",
            "reason": (
                "A bounded countermodel reattempt remains downstream of packet "
                "result review."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_packet",
            "reason": (
                "Source-map ladder work remains downstream unless a later "
                "reattempt result requires it."
            ),
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
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "The packet does not evaluate not-found status.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The pinned source remains candidate-only.",
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
            "reason": "The packet does not close QFT-GR.",
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


def _packet_findings() -> list[str]:
    return [
        (
            "The packet consumes the accepted refined-scope result review and "
            "prepares only a bounded countermodel reattempt packet."
        ),
        (
            "The later reattempt must use the pinned broader source/test pair, "
            "partial weak-pairing contract, and five-probe evaluation protocol."
        ),
        (
            "The packet retains found, not-found, and inconclusive as allowed "
            "later classifications without selecting any of them."
        ),
        (
            "No countermodel/no-go attempt is executed by this packet; result "
            "review is required before the downstream reattempt target."
        ),
        (
            "The strict toy positive witness remains valid only under its "
            "strict antecedents and is not refuted by the broader reattempt "
            "packet."
        ),
    ]


def _validation_policy(review: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_reattempt_packet_preparation",
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
        "inherited_scope_refinement_attempt_result_review_validation_policy": (
            review.get("validation_policy", {})
        ),
    }


def build_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    reattempt_probe_plan = _reattempt_probe_plan(review)
    allowed_classifications = _allowed_reattempt_classifications()
    decision_protocol = _reattempt_decision_protocol(review)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(review)

    acceptance_criteria = {
        "consumes_expected_refined_scope_result_review": (
            review.get("schema_id") == EXPECTED_RESULT_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_RESULT_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_RESULT_REVIEW_OUTCOME
            and review.get("result_review_classification")
            == EXPECTED_RESULT_REVIEW_CLASSIFICATION
            and review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "result_review_authorized_reattempt_packet_only": (
            review.get("accepted") is True
            and review.get("scope_refinement_attempt_result_review_accepted") is True
            and review.get("countermodel_reattempt_packet_authorized") is True
            and review.get("bounded_countermodel_reattempt_packet_authorized_only")
            is True
            and review.get("countermodel_reattempt_packet_prepared") is False
            and review.get("countermodel_reattempt_executed") is False
        ),
        "refined_scope_is_carried_exactly": (
            review.get("countermodel_lane_decidability_scope_accepted") is True
            and review.get("pinned_source_test_pair_id") == PINNED_SOURCE_TEST_PAIR_ID
            and review.get("pinned_weak_pairing_contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and review.get("pinned_evaluation_scope_id") == PINNED_EVALUATION_SCOPE_ID
        ),
        "source_test_and_pairing_payloads_available": (
            review.get("source_test_instantiation", {}).get("instantiation_id")
            == PINNED_SOURCE_TEST_PAIR_ID
            and review.get("weak_pairing_semantics", {}).get("contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and review.get("weak_pairing_semantics", {}).get("partiality_pinned")
            == "yes"
            and review.get("weak_pairing_semantics", {}).get("totality_claimed")
            == "no"
        ),
        "five_probe_protocol_prepared": (
            review.get("evaluation_scope", {}).get("evaluation_scope_id")
            == PINNED_EVALUATION_SCOPE_ID
            and review.get("evaluation_scope", {}).get("probe_count") == 5
            and len(reattempt_probe_plan) == 5
            and decision_protocol["probe_count"] == 5
        ),
        "allowed_classifications_retained_without_selection": (
            len(allowed_classifications) == 3
            and {
                row["classification"] for row in allowed_classifications
            }
            == {
                FOUND_CLASSIFICATION,
                NOT_FOUND_CLASSIFICATION,
                INCONCLUSIVE_CLASSIFICATION,
            }
            and all(row["selected_now"] == "no" for row in allowed_classifications)
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
        "does_not_execute_or_authorize_attempt_directly": (
            review.get("countermodel_attempt_after_scope_refinement_authorized")
            is False
            and review.get("countermodel_attempt_after_scope_refinement_executed")
            is False
            and review.get("countermodel_attempt_reauthorized") is False
            and review.get("countermodel_attempt_reexecuted") is False
        ),
        "no_countermodel_no_go_not_found_or_inconclusive_result_claim": (
            review.get("countermodel_result_claimed") is False
            and review.get("countermodel_exists_claimed") is False
            and review.get("countermodel_achieved") is False
            and review.get("no_go_result_claimed") is False
            and review.get("not_found_result_claimed") is False
            and review.get("inconclusive_result_claimed") is False
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
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION_REQUIRES_REMEDIATION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_scope_refinement_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_scope_refinement_attempt_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": review.get("schema_id"),
        "consumed_result_review_outcome_id": review.get("outcome_id"),
        "consumed_result_review_classification": review.get(
            "result_review_classification"
        ),
        "scope_refinement_attempt_result_review_accepted": (
            review.get("accepted") is True
        ),
        "countermodel_lane_decidability_scope_accepted": review.get(
            "countermodel_lane_decidability_scope_accepted"
        ),
        "countermodel_reattempt_packet_authorized_by_review": review.get(
            "countermodel_reattempt_packet_authorized"
        ),
        "countermodel_reattempt_packet_prepared": prepared,
        "countermodel_reattempt_packet_preparation_only": True,
        "countermodel_reattempt_packet_result_review_pending": prepared,
        "countermodel_reattempt_packet_result_reviewed": False,
        "countermodel_reattempt_authorized_by_packet": False,
        "countermodel_reattempt_executed": False,
        "countermodel_attempt_after_scope_refinement_authorized": False,
        "countermodel_attempt_after_scope_refinement_executed": False,
        "countermodel_attempt_reauthorized": False,
        "countermodel_attempt_reexecuted": False,
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": review.get("source_test_instantiation", {}),
        "weak_pairing_semantics": review.get("weak_pairing_semantics", {}),
        "evaluation_scope": review.get("evaluation_scope", {}),
        "reattempt_probe_plan": reattempt_probe_plan,
        "reattempt_probe_count": len(reattempt_probe_plan),
        "reattempt_decision_protocol": decision_protocol,
        "allowed_reattempt_classifications": allowed_classifications,
        "allowed_reattempt_classification_count": len(allowed_classifications),
        "found_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "inconclusive_classification_not_selected": True,
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
        "countermodel_reattempt_packet_is_not_strict_toy_witness_refutation": True,
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
        "packet_findings": _packet_findings(),
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
            "required for this routine bounded countermodel reattempt packet "
            "checkpoint. The release-index path remains not freshly Lean-"
            "validated, aggregate Lean is not run, and no aggregate Lean health "
            "claim is made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION"
        ),
        "packet_selected_next_target": NEXT_TARGET
        if prepared
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION"
        ),
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if prepared else 0,
        "selected_next_target_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION_RESULT_ONLY_NO_COUNTERMODEL_"
            "ATTEMPT_EXECUTION_NO_COUNTERMODEL_RESULT_CLAIM_NO_NO_GO_RESULT_"
            "CLAIM_NO_SOURCE_ADMISSIBILITY_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares only a bounded countermodel reattempt under "
            "the accepted refined source/test pair, partial weak-pairing "
            "contract, and five-probe evaluation protocol. It does not execute "
            "a countermodel/no-go attempt, does not claim a countermodel "
            "result, does not claim a no-go result, does not claim a not-found "
            "result, does not refute the accepted strict toy witness, "
            "preserves no source admissibility, no Bianchi compatibility, no "
            "semiclassical Einstein equation, no broad QFT-GR conservation, "
            "no QFT-GR closure, no empirical validation, no public submission, "
            "and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal model countermodel reattempt packet "
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
    payload = write_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction(
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
