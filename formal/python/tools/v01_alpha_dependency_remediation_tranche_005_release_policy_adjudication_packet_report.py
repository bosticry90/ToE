from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0"
)
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_"
    "PREPARED_WITH_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_AUDIT_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_AUDIT_RESULT_REVIEW_ACCEPTS_EXACT_"
    "LEAN_DEPENDENCY_EVIDENCE_AND_AUTHORIZES_RELEASE_POLICY_ADJUDICATION_PACKET_"
    "PREPARATION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_packet"
)
EXPECTED_TRANCHE_CLASSIFICATION = "audit_evidence_accepted_pending_release_policy_adjudication"
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
TRANCHE_003_STATUS = "documented_dependency_nonblocking"
TRANCHE_004_STATUS = "retained_release_blocking_source_map_blocker"
TRANCHE_004_FINDING_ID = "V01-ALPHA-DEP-REM-004"
TRANCHE_004_DEPENDENCY = (
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
TRANCHE_004_CURRENT_BLOCKER = "full_source_map_semantic_closure_not_authorized"
TRANCHE_004_RETAINED_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
TRANCHE_006_STATUS = "tracked_unresolved"
TRANCHE_006_FINDING_ID = "V01-ALPHA-DEP-REM-006"
TRANCHE_006_DEPENDENCY = "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0"

SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-005"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-005"
SELECTED_DEPENDENCY = "supplied_interface_alignment_semantics_construct_bridge_package_v0"
SELECTED_DEPENDENCY_CLASS = "lean_bridge_dependency"
LEAN_TARGET = (
    "ToeFormal.Bridges.EMQFTInterfaceAlignmentSemanticBridge."
    "supplied_interface_alignment_semantics_construct_bridge_package_v0"
)
LEAN_AUDIT_COMMAND = (
    "#print axioms ToeFormal.Bridges.EMQFTInterfaceAlignmentSemanticBridge."
    "supplied_interface_alignment_semantics_construct_bridge_package_v0"
)
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PROJECT_AXIOMS_USED: list[str] = []
NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_packet_result"
)

FORBIDDEN_EFFECTS = [
    "policy_adjudication_executed",
    "release_policy_decision_made",
    "remediation_closure_executed",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_readiness_pause_registered",
    "release_readiness_adjudication_prepared",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _exact_evidence(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("exact_lean_dependency_evidence", {}))


def _selected_obligation(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("selected_release_blocking_obligation", {}))


def _retained_tranche_004(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("retained_tranche_004_carry_forward", {}))


def _tranche_006(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("tranche_006_obligation_carry_forward", {}))


def _release_blockers(
    *,
    selected_obligation: dict[str, Any],
    retained_tranche_004: dict[str, Any],
    tranche_006: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "dependency_finding_id": TRANCHE_004_FINDING_ID,
            "dependency": retained_tranche_004.get("dependency", TRANCHE_004_DEPENDENCY),
            "dependency_class": retained_tranche_004.get(
                "dependency_class", "blocked_bridge_authorization_dependency"
            ),
            "status_carry_forward": TRANCHE_004_STATUS,
            "current_blocker": retained_tranche_004.get(
                "current_blocker", TRANCHE_004_CURRENT_BLOCKER
            ),
            "retained_blocker_reason": retained_tranche_004.get(
                "retained_blocker_reason", TRANCHE_004_RETAINED_REASON
            ),
            "modified_by_tranche_005_release_policy_packet": False,
        },
        {
            "dependency_finding_id": SELECTED_FINDING_ID,
            "dependency": selected_obligation.get("dependency", SELECTED_DEPENDENCY),
            "dependency_class": selected_obligation.get(
                "dependency_class", SELECTED_DEPENDENCY_CLASS
            ),
            "status_carry_forward": (
                "release_blocking_pending_tranche_005_release_policy_adjudication_packet_result_review"
            ),
            "modified_by_tranche_005_release_policy_packet": False,
        },
        {
            "dependency_finding_id": TRANCHE_006_FINDING_ID,
            "dependency": tranche_006.get("dependency", TRANCHE_006_DEPENDENCY),
            "dependency_class": tranche_006.get("dependency_class", "lean_bridge_dependency"),
            "status_carry_forward": TRANCHE_006_STATUS,
            "modified_by_tranche_005_release_policy_packet": False,
        },
    ]


def _other_blockers(
    *,
    retained_tranche_004: dict[str, Any],
    tranche_006: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "dependency_finding_id": TRANCHE_004_FINDING_ID,
            "dependency": retained_tranche_004.get("dependency", TRANCHE_004_DEPENDENCY),
            "dependency_class": retained_tranche_004.get(
                "dependency_class", "blocked_bridge_authorization_dependency"
            ),
            "status_carry_forward": TRANCHE_004_STATUS,
            "modified_by_tranche_005_release_policy_packet": False,
        },
        {
            "dependency_finding_id": TRANCHE_006_FINDING_ID,
            "dependency": tranche_006.get("dependency", TRANCHE_006_DEPENDENCY),
            "dependency_class": tranche_006.get("dependency_class", "lean_bridge_dependency"),
            "status_carry_forward": TRANCHE_006_STATUS,
            "modified_by_tranche_005_release_policy_packet": False,
        },
    ]


def _release_policy_acceptance_criteria() -> list[str]:
    return [
        "The later adjudication cites the exact accepted Lean dependency evidence for supplied_interface_alignment_semantics_construct_bridge_package_v0.",
        "The later adjudication evaluates propext, Classical.choice, and Quot.sound as standard Lean dependencies under the v0.1-alpha release policy.",
        "The later adjudication preserves project_axioms_used as an empty list unless new formal evidence is produced.",
        "The later adjudication records whether expert re-review is required for this standard Lean dependency posture.",
        "Any blocker downgrade is limited to tranche 005 and does not affect tranches 001, 002, 003, retained tranche 004, or tracked tranche 006.",
        "No theorem debt, proof debt, retained assumption, release-readiness, or promotion claim is inferred from policy acceptance alone.",
    ]


def _release_policy_failure_criteria() -> list[str]:
    return [
        "The later adjudication omits one or more of propext, Classical.choice, or Quot.sound.",
        "The later adjudication treats project_axioms_used = [] as theorem/proof-debt discharge.",
        "The later adjudication clears or moves tranche 005 without a recorded v0.1-alpha policy decision.",
        "The later adjudication modifies tranches 001, 002, 003, retained tranche 004, or tracked tranche 006.",
        "The later adjudication assembles the release packet, marks readiness, authorizes Phase 2, closes seams, validates empirically, or promotes the master action.",
        "The later adjudication skips result review before any blocker movement or remediation closure.",
    ]


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    evidence = _exact_evidence(result_review)
    selected_obligation = _selected_obligation(result_review)
    retained_tranche_004 = _retained_tranche_004(result_review)
    tranche_006 = _tranche_006(result_review)
    release_blockers = _release_blockers(
        selected_obligation=selected_obligation,
        retained_tranche_004=retained_tranche_004,
        tranche_006=tranche_006,
    )
    other_blockers = _other_blockers(
        retained_tranche_004=retained_tranche_004,
        tranche_006=tranche_006,
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    policy_question = (
        "Are [propext, Classical.choice, Quot.sound] acceptable standard Lean dependencies "
        "for tranche 005 / supplied_interface_alignment_semantics_construct_bridge_package_v0 "
        "under the v0.1-alpha release dependency policy, given project_axioms_used = []?"
    )

    acceptance_criteria = {
        "consumes_expected_audit_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "audit_result_review_accepted": result_review.get("accepted") is True,
        "audit_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "audit_result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": result_review.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET
        and result_review.get("lean_audit_target", {}).get("command") == LEAN_AUDIT_COMMAND,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get(
            "parsed_axioms"
        )
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty_preserved": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "prior_classification_requires_policy_adjudication": result_review.get(
            "tranche_005_audit_result_classification"
        )
        == EXPECTED_TRANCHE_CLASSIFICATION
        and result_review.get("release_policy_adjudication_packet_preparation_authorized")
        is True,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": result_review.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_004_retained_blocker_preserved": result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "tranche_006_tracked_unresolved": result_review.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and tranche_006.get("dependency_finding_id") == TRANCHE_006_FINDING_ID,
        "release_blockers_remain_tracked": [row.get("dependency_finding_id") for row in release_blockers]
        == [TRANCHE_004_FINDING_ID, SELECTED_FINDING_ID, TRANCHE_006_FINDING_ID],
        "other_blockers_unmodified": len(other_blockers) == 2
        and all(
            row.get("modified_by_tranche_005_release_policy_packet") is False
            for row in other_blockers
        ),
        "policy_question_defined": policy_question
        == (
            "Are [propext, Classical.choice, Quot.sound] acceptable standard Lean dependencies "
            "for tranche 005 / supplied_interface_alignment_semantics_construct_bridge_package_v0 "
            "under the v0.1-alpha release dependency policy, given project_axioms_used = []?"
        ),
        "release_policy_acceptance_criteria_defined": len(
            _release_policy_acceptance_criteria()
        )
        >= 6,
        "release_policy_failure_criteria_defined": len(_release_policy_failure_criteria())
        >= 6,
        "prepares_policy_adjudication_only": forbidden_effect_status[
            "policy_adjudication_executed"
        ]
        is False
        and forbidden_effect_status["release_policy_decision_made"] is False,
        "tranche_005_remains_blocking_pending_adjudication": True,
        "no_remediation_closure": forbidden_effect_status["remediation_closure_executed"]
        is False
        and forbidden_effect_status["broader_remediation_executed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "no_release_packet_assembly_or_readiness_marking": forbidden_effect_status[
            "release_packet_assembled"
        ]
        is False
        and forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "no_retained_assumption_discharge": forbidden_effect_status[
            "retained_assumptions_discharged"
        ]
        is False,
        "no_phase2_seam_empirical_or_master_action_authorization": all(
            forbidden_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "seam_closure_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_packet_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_BLOCKED",
        "consumes_audit_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_audit_result_review_pointer": _ptr(result_review_path),
        "consumed_audit_result_review_schema_id": result_review.get("schema_id"),
        "source_audit": result_review.get("consumes_audit"),
        "packet_scope": (
            "PREPARE_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_"
            "NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_tranche_004_release_blocker_carry_forward_required": True,
        "release_readiness_blocked_by_tranche_004": True,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_obligation_carry_forward": tranche_006,
        "global_release_readiness_still_blocked": True,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "lean_audit_target": {
            "lean_target": result_review.get("lean_audit_target", {}).get("lean_target"),
            "command": result_review.get("lean_audit_target", {}).get("command"),
            "exit_code": result_review.get("lean_audit_target", {}).get("exit_code"),
        },
        "accepted_lean_dependency_evidence": {
            "parsed_axioms": evidence.get("parsed_axioms"),
            "exact_axioms_or_dependencies_used": evidence.get(
                "exact_axioms_or_dependencies_used"
            ),
            "standard_lean_axioms_used": evidence.get("standard_lean_axioms_used"),
            "standard_lean_or_mathlib_axioms_used": evidence.get(
                "standard_lean_or_mathlib_axioms_used"
            ),
            "standard_lean_axiom_count": evidence.get("standard_lean_axiom_count"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
            "project_local_axioms_present": evidence.get("project_local_axioms_present"),
            "axiom_classification": evidence.get("axiom_classification"),
            "classification": evidence.get("classification"),
            "raw_output": evidence.get("raw_output"),
        },
        "policy_question": policy_question,
        "release_policy_acceptance_criteria": _release_policy_acceptance_criteria(),
        "release_policy_failure_criteria": _release_policy_failure_criteria(),
        "expert_re_review_requirement": (
            "A later adjudication must explicitly record whether expert re-review is required "
            "or waived for the standard Lean axiom posture of tranche 005."
        ),
        "blocker_may_be_downgraded_after_adjudication": (
            "only_if_later_policy_adjudication_accepts_standard_lean_axiom_posture"
        ),
        "blocker_downgrade_allowed_by_this_packet": False,
        "tranche_005_release_blocker_status": (
            "still_blocking_pending_release_policy_adjudication_packet_result_review"
        ),
        "policy_decision_made": False,
        "policy_adjudication_executed": False,
        "release_policy_adjudication_prepared": accepted,
        "remediation_closure_authorized": False,
        "remediation_closure_executed": False,
        "remediation_executed": False,
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_blockers,
        "other_release_blocking_obligation_count": len(other_blockers),
        "post_adjudication_review_target": (
            "review_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_result"
        ),
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "release_readiness_pause_registered": False,
        "release_readiness_adjudication_prepared": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_POLICY_PACKET",
        "selected_next_target_kind": "release_policy_adjudication_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The policy-adjudication packet must be reviewed before any policy decision can execute.",
            },
            {
                "target": (
                    "execute_v01_alpha_dependency_remediation_tranche_005_release_policy_"
                    "adjudication"
                ),
                "decision": "deferred",
                "reason": "The policy decision remains blocked until the packet result review authorizes execution.",
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": "Release readiness remains blocked by retained tranche 004 and tracked tranche 006.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 005 release-policy adjudication "
            "packet prepares a policy-decision wrapper only. It preserves exact Lean dependency "
            "evidence and empty project-local axiom evidence, carries tranche 004 as retained/"
            "release-blocking, and keeps tranche 006 tracked. It does not make the policy "
            "decision, close remediation, move blockers, assemble the release packet, mark "
            "v0.1-alpha readiness, discharge theorem/proof debt, discharge retained assumptions, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, "
            "promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 005 release-policy "
            "adjudication packet."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
