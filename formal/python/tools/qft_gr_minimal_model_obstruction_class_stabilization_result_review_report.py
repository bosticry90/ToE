from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_obstruction_class_stabilization_report import (
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PATTERN_STABILIZATION_SIGNAL,
    POSITIVE_WITNESS_TARGET,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    STATUS as EXPECTED_OBSTRUCTION_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_REVIEW_"
    "20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_DOMINANT_WEAK_PAIRING_OBSTRUCTION_CANDIDATE_AND_AUTHORIZES_"
    "POSITIVE_WITNESS_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_model_obstruction_class_stabilization_packet_result_review_"
    "accepts_dominant_weak_pairing_obstruction_candidate_and_authorizes_"
    "positive_witness_packet_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = POSITIVE_WITNESS_TARGET
NEXT_TARGET_KIND = (
    "qft_gr_minimal_positive_conservation_witness_packet_preparation_under_"
    "strict_toy_assumptions_only"
)
IMMEDIATE_RETEST_TARGET = (
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_"
    "post_retest_refinement_conservation_retest_refinement_refinement"
)
ORDINARY_REFINEMENT_TARGET = (
    "prepare_qft_gr_minimal_working_model_refinement_packet_after_post_retest_"
    "refinement_conservation_retest_refinement_refinement"
)
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction"
)
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source"
)
POSITIVE_WITNESS_BRIDGE_LAW = (
    "field_equation_residual_zero_plus_divergence_identity_plus_allowed_weak_"
    "pairing_plus_no_boundary_compact_support_implies_weak_conservation_against_"
    "allowed_tests"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_REVIEW_"
    "20260614_v0.json"
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
                "The obstruction-class packet is accepted as a decision-forcing "
                "classification step, so the next bounded action is preparation "
                "of the deliberately small positive conservation witness packet."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": (
                "The obstruction-class stabilization packet result-review target "
                "is consumed here."
            ),
        },
        {
            "target": IMMEDIATE_RETEST_TARGET,
            "decision": "not_authorized",
            "reason": (
                "The accepted pivot forbids another immediate conservation retest."
            ),
        },
        {
            "target": ORDINARY_REFINEMENT_TARGET,
            "decision": "not_authorized",
            "reason": (
                "The accepted pivot forbids another ordinary same-shaped model "
                "refinement packet."
            ),
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on_after_positive_witness_packet",
            "reason": (
                "Countermodel pressure remains a follow-on lane, not selected by "
                "this packet review."
            ),
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_after_countermodel_pressure",
            "reason": (
                "Source-map ladder reconstruction remains a later follow-on, not "
                "selected by this packet review."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The obstruction packet does not make a source admissibility claim.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The review authorizes a witness packet, not a conservation proof.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized_by_review",
            "reason": (
                "A witness may only be attempted after the next packet is prepared "
                "and reviewed; this review constructs no witness."
            ),
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
            "reason": "QFT-GR closure remains outside this bounded review.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _validation_policy(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_obstruction_class_stabilization_packet_result_review",
        "routine_packet_review_uses_bounded_target_relevant_validation_only": True,
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
        "inherited_packet_validation_policy": packet.get("validation_policy", {}),
        "full_suite_required_only_for_target_types": [
            "release_candidate",
            "integration_closeout",
            "aggregate_validation_diagnostic",
            "public_submission_readiness",
            "master_action_promotion_review",
            "governance_manifest_enrollment",
            "shared_test_infrastructure_change",
            "broad_dependency_or_tooling_change",
        ],
    }


def build_qft_gr_minimal_model_obstruction_class_stabilization_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(packet)
    packet_policy = packet.get("validation_policy", {})
    selected_obstructions = [
        row for row in packet.get("obstruction_map_rows", []) if row.get("selected")
    ]

    acceptance_criteria = {
        "consumes_expected_obstruction_packet": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
        ),
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_result_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "dominant_obstruction_candidate_accepted_for_selection": (
            packet.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and packet.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and packet.get("obstruction_status") == EXPECTED_OBSTRUCTION_STATUS
            and len(selected_obstructions) == 1
            and selected_obstructions[0].get("resolved") is False
        ),
        "obstruction_not_resolved_or_solved": (
            packet.get("dominant_obstruction_resolved") is False
            and packet.get("mathematical_resolution_claimed") is False
        ),
        "repeated_inconclusive_pattern_accepted_as_signal": (
            packet.get("attempt_chain_count") == 5
            and packet.get("latest_result_marked_inconclusive") is True
            and packet.get("pattern_stabilization_signal")
            == PATTERN_STABILIZATION_SIGNAL
            and packet.get("repeated_inconclusive_pattern_is_stabilization_signal")
            is True
        ),
        "supporting_obstructions_retained_unresolved": (
            packet.get("supporting_obstruction_count") == 7
            and all(
                row.get("resolved") is False
                for row in packet.get("obstruction_map_rows", [])
            )
        ),
        "no_immediate_retest_or_ordinary_refinement": (
            packet.get("immediate_retest_authorized") is False
            and packet.get("conservation_retest_rerun_authorized") is False
            and packet.get("ordinary_model_refinement_authorized") is False
        ),
        "positive_witness_lane_recommended_by_packet": (
            packet.get("positive_witness_lane_recommended") is True
            and packet.get("recommended_next_lane_after_review") == NEXT_TARGET
        ),
        "no_source_admissibility_conservation_or_bianchi_claim": (
            packet.get("source_admissibility_claimed") is False
            and packet.get("stress_energy_source_admissibility_claimed") is False
            and packet.get("conservation_claimed") is False
            and packet.get("conservation_proved") is False
            and packet.get("conservation_proof_object_constructed") is False
            and packet.get("conservation_witness_constructed") is False
            and packet.get("Bianchi_compatibility_claimed") is False
            and packet.get("semiclassical_einstein_equation_derived") is False
        ),
        "no_qft_gr_closure_empirical_public_or_promotion_claim": (
            packet.get("qft_gr_seam_closed") is False
            and packet.get("qft_gr_source_map_closure_claimed") is False
            and packet.get("empirical_validation_claimed") is False
            and packet.get("public_submission_authorized") is False
            and packet.get("master_action_promoted") is False
            and packet.get("master_action_promotion_authorized") is False
        ),
        "standing_validation_caveats_preserved": (
            packet.get("release_index_path_not_freshly_lean_validated") is True
            and packet.get("aggregate_lean_not_run") is True
            and packet.get("aggregate_lean_health_claimed") is False
            and packet_policy.get("full_pytest_required") is False
            and packet_policy.get("full_governance_suite_required") is False
            and packet_policy.get("full_aggregate_lean_required") is False
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
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_REVIEW"
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_MINIMAL_MODEL_OBSTRUCTION_CLASS_STABILIZATION_PACKET_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_obstruction_class_stabilization_packet_result_"
            "review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_model_obstruction_class_stabilization_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_minimal_model_obstruction_class_stabilization_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "packet_result_review_accepted": accepted,
        "obstruction_class_stabilization_packet_result_review_accepted": accepted,
        "obstruction_class_stabilization_packet_consumed": accepted,
        "decision_forcing_classification_step_accepted": accepted,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": EXPECTED_OBSTRUCTION_STATUS,
        "dominant_obstruction_candidate_accepted": accepted,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "obstruction_solved": False,
        "attempt_chain_count": packet.get("attempt_chain_count"),
        "latest_result_marked_inconclusive": packet.get(
            "latest_result_marked_inconclusive"
        ),
        "pattern_stabilization_signal": packet.get("pattern_stabilization_signal"),
        "repeated_inconclusive_pattern_accepted_as_stabilization_signal": accepted,
        "supporting_obstruction_count": packet.get("supporting_obstruction_count"),
        "supporting_obstructions_retained_unresolved": True,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
        "positive_witness_packet_authorized": accepted,
        "positive_witness_packet_prepared_by_review": False,
        "positive_witness_attempt_authorized": False,
        "positive_witness_attempt_executed": False,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "countermodel_lane_retained_as_follow_on": True,
        "countermodel_packet_authorized": False,
        "source_map_ladder_lane_retained_as_follow_on": True,
        "source_map_ladder_packet_authorized": False,
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
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "validation_policy": validation_policy,
        "validation_posture": {
            "focused_result_review_current_target_registry_gates": (
                "required_for_checkpoint"
            ),
            "adjacent_minimal_model_nonclaim_gates": "required_bounded_subset",
            "bounded_lean_substitute_result_review_frontier": (
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
            "required for this routine bounded packet-result-review checkpoint. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_"
            "STRICT_TOY_ASSUMPTIONS_ONLY_NO_IMMEDIATE_RETEST_NO_ORDINARY_"
            "MODEL_REFINEMENT_NO_SOURCE_ADMISSIBILITY_CONSERVATION_PROOF_WITNESS_"
            "BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_VALIDATION_"
            "PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the obstruction-class stabilization "
            "packet as a decision-forcing classification step. It treats "
            "weak_pairing_domain_obstruction as a dominant obstruction candidate "
            "for next-target selection, not as solved mathematics. It authorizes "
            "only preparation of a strict toy positive conservation witness "
            "packet and authorizes no immediate retest, no ordinary model "
            "refinement, no conservation proof, no conservation proof object, no "
            "conservation witness, no source admissibility, no Bianchi "
            "compatibility, no semiclassical Einstein equation, no QFT-GR "
            "closure, no empirical validation, no public submission, and no "
            "master-action promotion."
        ),
    }


def write_qft_gr_minimal_model_obstruction_class_stabilization_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_obstruction_class_stabilization_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal-model obstruction-class stabilization "
            "packet result review."
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
    payload = write_qft_gr_minimal_model_obstruction_class_stabilization_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_model_obstruction_class_stabilization_result_review: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
