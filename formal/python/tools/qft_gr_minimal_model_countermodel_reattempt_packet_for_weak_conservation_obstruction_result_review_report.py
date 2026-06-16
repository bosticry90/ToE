from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_report import (
    COUNTERMODEL_REATTEMPT_TARGET,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    FOUND_CLASSIFICATION,
    INCONCLUSIVE_CLASSIFICATION,
    LEAN_PACKET_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    NOT_FOUND_CLASSIFICATION,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PINNED_EVALUATION_SCOPE_ID,
    PINNED_SOURCE_TEST_PAIR_ID,
    PINNED_WEAK_PAIRING_CONTRACT_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_20260615_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
    "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_"
    "BOUNDED_COUNTERMODEL_REATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_"
    "obstruction_result_review_accepts_packet_and_authorizes_bounded_"
    "countermodel_reattempt_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = COUNTERMODEL_REATTEMPT_TARGET
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_"
    "weak_conservation_obstruction_execution"
)
PREFERRED_BUT_NOT_USED_REATTEMPT_TARGET = (
    "execute_qft_gr_minimal_model_countermodel_reattempt_for_weak_"
    "conservation_obstruction"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
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
        "QFTGRMinimalModelCountermodelReattemptPacketForWeakConservation"
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
                "The reattempt packet is accepted, so the only authorized "
                "next action is the exact bounded countermodel reattempt "
                "target already encoded by the packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The reattempt-packet result-review target is consumed here.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_not_selected_by_this_review",
            "reason": (
                "Source-map ladder work remains downstream unless the later "
                "bounded reattempt selects not-found under pinned scope or "
                "requires source-map clarification."
            ),
        },
        {
            "target": PREFERRED_BUT_NOT_USED_REATTEMPT_TARGET,
            "decision": "not_authorized_target_name_drift",
            "reason": (
                "This preferred shorter name is not selected because the "
                "review must authorize exactly the target already encoded in "
                "the prepared packet."
            ),
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized",
            "reason": "The review accepts a packet only; no countermodel is found.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized",
            "reason": "No no-go result is found or claimed by this review.",
        },
        {
            "target": "claim_countermodel_not_found",
            "decision": "not_authorized",
            "reason": "The review does not evaluate not-found status.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The pinned source remains candidate-only.",
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
            "reason": "The review authorizes a bounded reattempt only, not closure.",
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
            "The prepared reattempt packet consumes the accepted refined "
            "countermodel scope and is accepted as a bounded setup for the "
            "next pressure test."
        ),
        (
            "The review authorizes exactly the packet-encoded downstream "
            "target execute_qft_gr_minimal_model_countermodel_attempt_after_"
            "scope_refinement_for_weak_conservation_obstruction."
        ),
        (
            "Found, not-found under pinned scope, and inconclusive remain "
            "allowed later classifications, but none is selected by this "
            "review."
        ),
        (
            "The strict toy positive witness remains valid only under its "
            "strict antecedents and is not refuted by the broader reattempt "
            "authorization."
        ),
        (
            "The review makes no countermodel/no-go/not-found result claim "
            "and preserves no source admissibility, no broad QFT-GR "
            "conservation, and no QFT-GR closure."
        ),
    ]


def _validation_policy(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_reattempt_packet_result_review",
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
        "inherited_reattempt_packet_validation_policy": packet.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    allowed_classifications = packet.get("allowed_reattempt_classifications", [])
    classification_set = {row.get("classification") for row in allowed_classifications}
    validation_policy = _validation_policy(packet)
    encoded_downstream_target_seen = any(
        row.get("target") == NEXT_TARGET
        and row.get("decision") == "not_authorized_until_reattempt_packet_result_review"
        for row in packet.get("candidate_next_targets", [])
    )

    acceptance_criteria = {
        "consumes_expected_reattempt_packet": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
            and packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME
            and packet.get("packet_classification") == EXPECTED_PACKET_CLASSIFICATION
            and packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "packet_prepared_pending_result_review": (
            packet.get("prepared") is True
            and packet.get("accepted") is True
            and packet.get("countermodel_reattempt_packet_prepared") is True
            and packet.get("countermodel_reattempt_packet_preparation_only") is True
            and packet.get("countermodel_reattempt_packet_result_review_pending")
            is True
            and packet.get("countermodel_reattempt_packet_result_reviewed") is False
        ),
        "encoded_downstream_target_preserved": (
            encoded_downstream_target_seen
            and NEXT_TARGET
            == "execute_qft_gr_minimal_model_countermodel_attempt_after_scope_refinement_for_weak_conservation_obstruction"
            and PREFERRED_BUT_NOT_USED_REATTEMPT_TARGET != NEXT_TARGET
        ),
        "pinned_scope_and_protocol_carried": (
            packet.get("pinned_source_test_pair_id") == PINNED_SOURCE_TEST_PAIR_ID
            and packet.get("pinned_weak_pairing_contract_id")
            == PINNED_WEAK_PAIRING_CONTRACT_ID
            and packet.get("pinned_evaluation_scope_id") == PINNED_EVALUATION_SCOPE_ID
            and packet.get("reattempt_probe_count") == 5
            and packet.get("reattempt_decision_protocol", {}).get("probe_count") == 5
        ),
        "allowed_classifications_retained_unselected": (
            len(allowed_classifications) == 3
            and classification_set
            == {
                FOUND_CLASSIFICATION,
                NOT_FOUND_CLASSIFICATION,
                INCONCLUSIVE_CLASSIFICATION,
            }
            and all(row.get("selected_now") == "no" for row in allowed_classifications)
            and packet.get("found_classification_not_selected") is True
            and packet.get("not_found_classification_not_selected") is True
            and packet.get("inconclusive_classification_not_selected") is True
        ),
        "review_selects_exact_downstream_target_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "strict_toy_witness_preserved_not_refuted": (
            packet.get("strict_toy_witness_preserved") is True
            and packet.get("strict_toy_witness_accepted") is True
            and packet.get("strict_toy_assumptions_only") is True
            and packet.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "no_countermodel_no_go_not_found_or_inconclusive_result_claim": (
            packet.get("countermodel_result_claimed") is False
            and packet.get("countermodel_exists_claimed") is False
            and packet.get("countermodel_achieved") is False
            and packet.get("no_go_result_claimed") is False
            and packet.get("not_found_result_claimed") is False
            and packet.get("inconclusive_result_claimed") is False
        ),
        "no_source_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            packet.get("source_admissibility_claimed") is False
            and packet.get("Bianchi_compatibility_claimed") is False
            and packet.get("semiclassical_einstein_equation_derived") is False
            and packet.get("qft_gr_seam_closed") is False
            and packet.get("qft_gr_source_map_closure_claimed") is False
            and packet.get("empirical_validation_claimed") is False
            and packet.get("public_submission_authorized") is False
            and packet.get("master_action_promoted") is False
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
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_"
            "WEAK_CONSERVATION_OBSTRUCTION_RESULT_REVIEW"
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
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_REATTEMPT_PACKET_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_"
            "conservation_obstruction_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_reattempt_packet_id": EXPECTED_PACKET_ID,
        "consumes_reattempt_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "reattempt_packet_result_review_accepted": accepted,
        "reattempt_packet_consumed": accepted,
        "reattempt_packet_prepared": packet.get("countermodel_reattempt_packet_prepared")
        is True,
        "reattempt_packet_result_reviewed": accepted,
        "reattempt_packet_result_review_pending": False,
        "countermodel_reattempt_packet_result_review_accepted": accepted,
        "countermodel_reattempt_packet_result_reviewed": accepted,
        "countermodel_reattempt_packet_result_review_pending": False,
        "countermodel_reattempt_authorized_by_packet_review": accepted,
        "countermodel_reattempt_authorized_by_packet": False,
        "countermodel_reattempt_executed": False,
        "countermodel_attempt_after_scope_refinement_authorized": accepted,
        "countermodel_attempt_after_scope_refinement_executed": False,
        "countermodel_attempt_reauthorized": accepted,
        "countermodel_attempt_reexecuted": False,
        "target_name_drift_prevented": True,
        "encoded_downstream_target": NEXT_TARGET,
        "preferred_but_not_used_reattempt_target": PREFERRED_BUT_NOT_USED_REATTEMPT_TARGET,
        "review_authorizes_exact_packet_downstream_target": accepted,
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "source_test_instantiation": packet.get("source_test_instantiation", {}),
        "weak_pairing_semantics": packet.get("weak_pairing_semantics", {}),
        "evaluation_scope": packet.get("evaluation_scope", {}),
        "reattempt_probe_plan": packet.get("reattempt_probe_plan", []),
        "reattempt_probe_count": packet.get("reattempt_probe_count"),
        "reattempt_decision_protocol": packet.get("reattempt_decision_protocol", {}),
        "allowed_reattempt_classifications": allowed_classifications,
        "allowed_reattempt_classification_count": len(allowed_classifications),
        "found_classification_not_selected": True,
        "not_found_classification_not_selected": True,
        "inconclusive_classification_not_selected": True,
        "countermodel_not_found_means_under_pinned_scope_only": True,
        "selected_countermodel_criterion_count": 0,
        "selected_no_go_criterion_count": 0,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "inconclusive_result_claimed": False,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": packet.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "countermodel_reattempt_review_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": packet.get("dominant_obstruction_candidate"),
        "canonical_obstruction_id": packet.get("canonical_obstruction_id"),
        "obstruction_status": packet.get("obstruction_status"),
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
            "required for this routine bounded reattempt-packet result-review "
            "checkpoint. The release-index path remains not freshly Lean-"
            "validated, aggregate Lean is not run, and no aggregate Lean health "
            "claim is made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lean_result_review_file": _ptr(LEAN_REVIEW_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_AFTER_SCOPE_"
            "REFINEMENT_FOR_WEAK_CONSERVATION_OBSTRUCTION_ONLY_NO_RESULT_"
            "CLAIM_UNTIL_ATTEMPT_EXECUTION_AND_RESULT_REVIEW_NO_SOURCE_"
            "ADMISSIBILITY_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared reattempt packet and "
            "authorizes only the exact bounded countermodel reattempt target "
            "already encoded by the packet. It does not execute the reattempt, "
            "does not claim a countermodel result, does not claim a no-go "
            "result, does not claim a not-found result, does not refute the "
            "accepted strict toy witness, preserves no source admissibility, "
            "no Bianchi compatibility, no semiclassical Einstein equation, no "
            "broad QFT-GR conservation, no QFT-GR closure, no empirical "
            "validation, no public submission, and no master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the bounded QFT-GR minimal model countermodel reattempt "
            "packet result review for the weak-conservation obstruction."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_minimal_model_countermodel_reattempt_packet_for_weak_conservation_obstruction_result_review(
        packet_path=packet_path,
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
