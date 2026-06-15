from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_report import (
    ATTEMPT_TARGET,
    CANONICAL_OBSTRUCTION_ID,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    IMMEDIATE_RETEST_TARGET,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    ORDINARY_REFINEMENT_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-14T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_RESULT_REVIEW_20260614_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_TOY_"
    "ASSUMPTIONS_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_"
    "WITNESS_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_"
    "assumptions_result_review_accepts_packet_and_authorizes_bounded_witness_"
    "attempt_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = ATTEMPT_TARGET
NEXT_TARGET_KIND = (
    "qft_gr_minimal_positive_conservation_witness_attempt_under_strict_toy_"
    "assumptions_execution"
)
COUNTERMODEL_TARGET = (
    "prepare_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction"
)
SOURCE_MAP_LADDER_TARGET = (
    "prepare_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source"
)
OBSTRUCTION_STATUS = "stabilized_for_next_target_selection_not_resolved"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_"
        "TOY_ASSUMPTIONS_RESULT_REVIEW_20260614_v0.json"
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
                "The strict toy positive conservation witness packet is "
                "accepted, so the only authorized next action is the bounded "
                "witness attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The packet result-review target is consumed here.",
        },
        {
            "target": IMMEDIATE_RETEST_TARGET,
            "decision": "not_authorized",
            "reason": "The decision-forcing pivot still forbids immediate conservation retest.",
        },
        {
            "target": ORDINARY_REFINEMENT_TARGET,
            "decision": "not_authorized",
            "reason": "Ordinary same-shaped model refinement remains out of scope.",
        },
        {
            "target": COUNTERMODEL_TARGET,
            "decision": "retained_follow_on_after_witness_attempt_review",
            "reason": "Countermodel pressure remains a later lane, not selected by this review.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_after_countermodel_pressure",
            "reason": "Source-map ladder reconstruction remains a later follow-on.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The packet and this review do not claim source admissibility.",
        },
        {
            "target": "claim_qft_gr_conservation_witness_constructed",
            "decision": "not_authorized_by_review",
            "reason": "The witness attempt is authorized but has not been executed.",
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
        "checkpoint_type": "routine_positive_conservation_witness_packet_result_review",
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
    }


def build_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(packet)
    packet_policy = packet.get("validation_policy", {})
    component_names = {
        row.get("component") for row in packet.get("strict_toy_bridge_components", [])
    }
    criteria = packet.get("pass_fail_inconclusive_criteria", {})

    acceptance_criteria = {
        "consumes_expected_positive_witness_packet": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
            and packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME
            and packet.get("packet_classification") == EXPECTED_PACKET_CLASSIFICATION
        ),
        "packet_selected_this_result_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_defines_strict_toy_bridge": (
            packet.get("strict_toy_assumptions_only") is True
            and packet.get("strict_toy_bridge_component_count") == 8
            and component_names
            == {
                "allowed_weak_test_class",
                "weak_pairing",
                "source_object",
                "divergence_pairing",
                "field_equation_residual",
                "divergence_identity",
                "compact_support_no_boundary_condition",
                "pass_fail_inconclusive_criteria",
            }
            and packet.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "pass_fail_inconclusive_criteria_present": (
            set(criteria) == {"pass", "fail", "inconclusive"}
            and all(criteria.values())
        ),
        "obstruction_candidate_carried_unresolved": (
            packet.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and packet.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and packet.get("obstruction_status") == OBSTRUCTION_STATUS
            and packet.get("dominant_obstruction_resolved") is False
            and packet.get("mathematical_resolution_claimed") is False
        ),
        "packet_has_not_executed_witness_attempt": (
            packet.get("positive_witness_attempt_executed") is False
            and packet.get("positive_witness_attempt_authorized_by_packet") is False
        ),
        "review_selects_bounded_witness_attempt_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "no_immediate_retest_or_ordinary_refinement": (
            packet.get("immediate_retest_authorized") is False
            and packet.get("conservation_retest_rerun_authorized") is False
            and packet.get("ordinary_model_refinement_authorized") is False
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
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_RESULT_REVIEW"
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
            "QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_PACKET_UNDER_STRICT_"
            "TOY_ASSUMPTIONS_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_positive_conservation_witness_packet_under_strict_"
            "toy_assumptions_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_positive_conservation_witness_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_minimal_positive_conservation_witness_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "packet_result_review_accepted": accepted,
        "positive_witness_packet_result_review_accepted": accepted,
        "positive_witness_packet_consumed": accepted,
        "positive_witness_packet_prepared": packet.get("positive_witness_packet_prepared"),
        "strict_toy_assumptions_only": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "allowed_weak_test_class_id": packet.get("allowed_weak_test_class_id"),
        "weak_pairing_id": packet.get("weak_pairing_id"),
        "source_object_id": packet.get("source_object_id"),
        "divergence_pairing_id": packet.get("divergence_pairing_id"),
        "field_equation_residual_id": packet.get("field_equation_residual_id"),
        "divergence_identity_id": packet.get("divergence_identity_id"),
        "no_boundary_condition_id": packet.get("no_boundary_condition_id"),
        "pass_fail_inconclusive_criteria": criteria,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "positive_witness_attempt_authorized": accepted,
        "bounded_witness_attempt_authorized_only": accepted,
        "positive_witness_attempt_executed": False,
        "positive_witness_attempt_result_reviewed": False,
        "positive_witness_packet_prepared_by_review": False,
        "immediate_retest_authorized": False,
        "conservation_retest_rerun_authorized": False,
        "ordinary_model_refinement_authorized": False,
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
            "EXECUTE_QFT_GR_MINIMAL_POSITIVE_CONSERVATION_WITNESS_ATTEMPT_"
            "UNDER_STRICT_TOY_ASSUMPTIONS_ONLY_NO_IMMEDIATE_RETEST_NO_ORDINARY_"
            "MODEL_REFINEMENT_NO_SOURCE_ADMISSIBILITY_NO_CONSERVATION_WITNESS_"
            "YET_NO_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_EMPIRICAL_"
            "VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared strict toy positive "
            "conservation witness packet and authorizes only the bounded "
            "witness attempt under those assumptions. It does not execute the "
            "attempt, does not construct a conservation proof object or "
            "conservation witness, does not claim source admissibility, does "
            "not claim Bianchi compatibility, does not derive a semiclassical "
            "Einstein equation, does not close QFT-GR, does not validate "
            "empirically, does not authorize public submission, and does not "
            "promote the master action."
        ),
    }


def write_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal positive conservation witness packet "
            "result review under strict toy assumptions."
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
    payload = write_qft_gr_minimal_positive_conservation_witness_packet_under_strict_toy_assumptions_result_review(
        packet_path=packet_path,
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
