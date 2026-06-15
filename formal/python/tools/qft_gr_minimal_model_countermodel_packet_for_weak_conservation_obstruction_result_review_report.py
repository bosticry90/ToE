from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_report import (
    CANONICAL_OBSTRUCTION_ID,
    COUNTERMODEL_ATTEMPT_TARGET,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    DOMINANT_OBSTRUCTION_CANDIDATE,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OBSTRUCTION_STATUS,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    POSITIVE_WITNESS_BRIDGE_LAW,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-15T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_RESULT_REVIEW_20260615_v0"
)
REVIEW_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
    "OBSTRUCTION_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_"
    "COUNTERMODEL_ATTEMPT_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
    "obstruction_result_review_accepts_packet_and_authorizes_bounded_"
    "countermodel_attempt_only"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = COUNTERMODEL_ATTEMPT_TARGET
NEXT_TARGET_KIND = (
    "qft_gr_minimal_model_countermodel_attempt_for_weak_conservation_"
    "obstruction_execution"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
        "OBSTRUCTION_RESULT_REVIEW_20260615_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalModelCountermodelPacketForWeakConservationObstructionResultReview.lean"
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
                "The prepared countermodel/no-go criteria are accepted, so "
                "the only authorized next action is the bounded countermodel "
                "attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The countermodel packet result-review target is consumed here.",
        },
        {
            "target": "claim_countermodel_exists",
            "decision": "not_authorized_by_review",
            "reason": "The review authorizes an attempt only; no countermodel result exists yet.",
        },
        {
            "target": "claim_no_go_result",
            "decision": "not_authorized_by_review",
            "reason": "No no-go result is claimed before the bounded attempt is executed.",
        },
        {
            "target": "execute_immediate_conservation_retest",
            "decision": "not_authorized",
            "reason": "The decision-forcing pivot still forbids another immediate retest.",
        },
        {
            "target": SOURCE_MAP_LADDER_TARGET,
            "decision": "retained_follow_on_after_countermodel_attempt_review",
            "reason": "Source-map ladder work remains downstream of countermodel pressure.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The packet review cannot establish source admissibility.",
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
            "reason": "A packet review is not QFT-GR closure.",
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


def _validation_policy(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_minimal_model_countermodel_packet_result_review",
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
        "inherited_countermodel_packet_validation_policy": packet.get(
            "validation_policy", {}
        ),
    }


def build_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    validation_policy = _validation_policy(packet)
    packet_policy = packet.get("validation_policy", {})
    criteria = packet.get("countermodel_or_no_go_criteria", [])
    attempt_classifications = packet.get("attempt_classifications", [])

    acceptance_criteria = {
        "consumes_expected_countermodel_packet": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
            and packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME
            and packet.get("packet_classification") == EXPECTED_PACKET_CLASSIFICATION
            and packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "accepts_countermodel_or_no_go_criteria_only": (
            packet.get("countermodel_packet_prepared") is True
            and packet.get("countermodel_or_no_go_criteria_count") == 7
            and len(criteria) == 7
            and packet.get("attempt_classification_count") == 3
            and len(attempt_classifications) == 3
        ),
        "strict_toy_witness_preserved_not_refuted": (
            packet.get("countermodel_packet_is_not_strict_toy_witness_refutation")
            is True
            and packet.get("strict_toy_witness_preserved") is True
            and packet.get("strict_toy_witness_accepted") is True
            and packet.get("strict_toy_assumptions_only") is True
            and packet.get("positive_witness_bridge_law_scope")
            == POSITIVE_WITNESS_BRIDGE_LAW
        ),
        "obstruction_candidate_carried_unresolved": (
            packet.get("dominant_obstruction_candidate")
            == DOMINANT_OBSTRUCTION_CANDIDATE
            and packet.get("canonical_obstruction_id") == CANONICAL_OBSTRUCTION_ID
            and packet.get("obstruction_status") == OBSTRUCTION_STATUS
            and packet.get("dominant_obstruction_resolved") is False
            and packet.get("mathematical_resolution_claimed") is False
        ),
        "review_selects_bounded_countermodel_attempt_only": _selected_targets(
            candidate_next_targets
        )
        == [NEXT_TARGET],
        "does_not_execute_or_claim_countermodel": (
            packet.get("countermodel_attempt_authorized") is False
            and packet.get("countermodel_attempt_executed") is False
            and packet.get("countermodel_result_claimed") is False
            and packet.get("countermodel_achieved") is False
            and packet.get("no_go_result_claimed") is False
            and packet.get("inconclusive_result_claimed") is False
        ),
        "no_immediate_retest_source_map_ladder_or_refinement": (
            packet.get("immediate_retest_authorized") is False
            and packet.get("source_map_ladder_packet_authorized") is False
            and packet.get("ordinary_model_refinement_authorized") is False
        ),
        "no_source_admissibility_or_broad_conservation": (
            packet.get("source_admissibility_can_be_considered") is False
            and packet.get("source_admissibility_claimed") is False
            and packet.get("stress_energy_source_admissibility_claimed") is False
            and packet.get("conservation_claimed") is False
            and packet.get("conservation_proved") is False
            and packet.get("conservation_proof_object_constructed") is False
            and packet.get("conservation_witness_constructed") is False
            and packet.get("full_qft_gr_conservation_claimed") is False
            and packet.get("unbounded_conservation_proved") is False
        ),
        "no_bianchi_semiclassical_closure_empirical_public_or_promotion": (
            packet.get("Bianchi_compatibility_claimed") is False
            and packet.get("semiclassical_einstein_equation_derived") is False
            and packet.get("qft_gr_seam_closed") is False
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
        else (
            "REMEDIATE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_"
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
            "QFT_GR_MINIMAL_MODEL_COUNTERMODEL_PACKET_FOR_WEAK_CONSERVATION_"
            "OBSTRUCTION_RESULT_REVIEW_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_minimal_model_countermodel_packet_for_weak_conservation_"
            "obstruction_result_review_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_countermodel_packet_id": EXPECTED_PACKET_ID,
        "consumes_countermodel_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "countermodel_packet_result_review_accepted": accepted,
        "countermodel_packet_consumed": accepted,
        "countermodel_packet_accepted": accepted,
        "countermodel_packet_prepared": packet.get("countermodel_packet_prepared"),
        "countermodel_or_no_go_criteria_accepted": accepted,
        "countermodel_or_no_go_criteria": criteria,
        "countermodel_or_no_go_criteria_count": len(criteria),
        "attempt_classifications": attempt_classifications,
        "attempt_classification_count": len(attempt_classifications),
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": packet.get("strict_toy_witness_accepted"),
        "strict_toy_assumptions_only": True,
        "countermodel_packet_is_not_strict_toy_witness_refutation": True,
        "positive_witness_bridge_law_scope": POSITIVE_WITNESS_BRIDGE_LAW,
        "dominant_obstruction_candidate": DOMINANT_OBSTRUCTION_CANDIDATE,
        "canonical_obstruction_id": CANONICAL_OBSTRUCTION_ID,
        "obstruction_status": OBSTRUCTION_STATUS,
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "bounded_countermodel_attempt_authorized_only": accepted,
        "countermodel_attempt_authorized": accepted,
        "countermodel_attempt_executed": False,
        "countermodel_result_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "inconclusive_result_claimed": False,
        "countermodel_exists_claimed": False,
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
            "required for this routine bounded countermodel-packet result-"
            "review checkpoint. The release-index path remains not freshly "
            "Lean-validated, aggregate Lean is not run, and no aggregate Lean "
            "health claim is made."
        ),
        "lean_result_review_file": _ptr(LEAN_REVIEW_PATH),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "result_review_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_QFT_GR_MINIMAL_MODEL_COUNTERMODEL_ATTEMPT_FOR_WEAK_"
            "CONSERVATION_OBSTRUCTION_ONLY_NO_COUNTERMODEL_RESULT_CLAIM_NO_"
            "SOURCE_ADMISSIBILITY_NO_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_"
            "CLOSURE_EMPIRICAL_VALIDATION_PUBLIC_SUBMISSION_OR_MASTER_ACTION_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the prepared countermodel/no-go "
            "criteria packet and authorizes only the bounded countermodel "
            "attempt for the broader weak-pairing/source-candidate family. It "
            "does not execute the attempt, does not claim a countermodel or "
            "no-go result exists, does not refute the accepted strict toy "
            "witness, does not claim source admissibility, does not claim "
            "Bianchi compatibility, does not derive a semiclassical Einstein "
            "equation, does not claim broad QFT-GR conservation, does not "
            "close QFT-GR, does not validate empirically, does not authorize "
            "public submission, and does not promote the master action."
        ),
    }


def write_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal model countermodel packet result "
            "review for the weak-conservation obstruction."
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
    payload = write_qft_gr_minimal_model_countermodel_packet_for_weak_conservation_obstruction_result_review(
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
