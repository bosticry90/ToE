from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_20260515_v0"
)
PACKET_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_AUDIT_RESULT_REVIEW_ACCEPTS_REAL_"
    "SOURCE_MAP_AUTHORIZATION_BLOCKER_AND_AUTHORIZES_REMEDIATION_PLANNING_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_"
    "remediation_packet"
)

TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
TRANCHE_003_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-004"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-004"
SELECTED_DEPENDENCY = (
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
SELECTED_DEPENDENCY_CLASS = "blocked_bridge_authorization_dependency"
REQUIRED_REMEDIATION_TYPE = "source_map_authorization_and_dependency_adjudication"
CURRENT_BLOCKER = "full_source_map_semantic_closure_not_authorized"
BLOCKER_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
LEAN_AXIOMS_USED: list[str] = []
PROJECT_AXIOMS_USED: list[str] = []

REQUIRED_WITNESS_CHAIN_EVIDENCE = [
    "renormalization_validity_witness",
    "finite_stress_energy_tensor_witness",
    "conservation_witness",
    "bianchi_compatibility_witness",
    "einstein_coupling_witness",
    "weak_curvature_source_identification_witness",
    "poisson_recovery_witness",
    "newtonian_weak_field_recovery_witness",
    "semiclassical_einstein_equation_witness",
    "qft_gr_source_map_closure_witness",
]

REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_EVIDENCE = [
    "positive_full_source_map_semantic_closure_authorization_readout",
    "witness_chain_complete_for_all_required_qft_gr_source_map_layers",
    "semantic_closure_proof_or_equivalent_reviewed_evidence",
    "no_reinterpretation_of_negative_authorization_marker_as_closure",
    "expert_review_acceptance_before_any_blocker_downgrade",
]

AUTHORIZATION_CONDITIONS = [
    "all_required_witness_chain_evidence_is_present_and_reviewed",
    "source_map_semantic_closure_authorization_status_is_positive",
    "negative_authorization_marker_is_replaced_only_by_reviewed_positive_evidence",
    "lean_dependency_audit_remains_project_axiom_free",
    "expert_re_review_accepts_any_attempted_source_map_authorization_change",
    "result_review_accepts_evidence_before_blocker_movement_is_considered",
]

FAILURE_CONDITIONS = [
    "any_required_witness_chain_evidence_remains_absent",
    "source_map_semantic_closure_authorization_status_remains_not_authorized",
    "documentation_only_text_is_used_to_claim_source_map_closure",
    "project_local_axioms_are_introduced_without_escalation",
    "expert_re_review_is_required_but_not_completed",
    "packet_or_execution_attempts_release_readiness_or_blocker_movement",
]

NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_"
    "remediation_packet_result"
)
POST_REMEDIATION_ADJUDICATION_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_"
    "remediation_result"
)

FORBIDDEN_EFFECTS = [
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "witness_chain_constructed",
    "remediation_execution_authorized",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
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


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    source_map_posture = dict(result_review.get("accepted_source_map_authorization_posture", {}))
    lean_posture = dict(result_review.get("accepted_lean_dependency_posture", {}))
    release_blockers = _release_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    documentation_role = {
        "documentation_can_help": True,
        "documentation_purpose": (
            "Document the retained source-map authorization blocker, required evidence, "
            "and fail-closed release-readiness implications."
        ),
        "documentation_alone_can_clear_blocker": False,
        "documentation_packet_prepared_by_this_packet": False,
    }
    lean_theorem_work_requirement = {
        "lean_theorem_work_required": "likely_required_for_positive_source_map_authorization",
        "reason": (
            "A positive source-map authorization would need reviewed witness-chain and "
            "semantic-closure evidence; the current Lean audit only shows no axiom dependency."
        ),
        "lean_theorem_work_executed_by_this_packet": False,
    }
    expert_re_review_requirement = {
        "expert_re_review_required": True,
        "required_before": [
            "source_map_authorization_status_change",
            "blocker_downgrade_or_movement",
            "release_readiness_adjudication_relying_on_tranche_004",
        ],
        "expert_re_review_executed_by_this_packet": False,
    }

    planning_scope = {
        "scope_kind": "SOURCE_MAP_AUTHORIZATION_REMEDIATION_PLANNING_ONLY",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_dependency_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "current_blocker": CURRENT_BLOCKER,
        "blocker_reason": BLOCKER_REASON,
        "required_remediation_type": REQUIRED_REMEDIATION_TYPE,
        "required_witness_chain_evidence": REQUIRED_WITNESS_CHAIN_EVIDENCE,
        "required_source_map_semantic_closure_evidence": (
            REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_EVIDENCE
        ),
        "authorization_conditions": AUTHORIZATION_CONDITIONS,
        "failure_conditions": FAILURE_CONDITIONS,
        "allowed_future_branches_after_packet_review": [
            "bounded_source_map_witness_chain_evidence_construction_attempt",
            "documentation_only_retained_blocker_packet",
            "fail_closed_release_readiness_blocker_declaration",
        ],
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
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
        "tranche_004_selected_only": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and result_review.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and result_review.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_obligation_expected": selected_obligation.get("dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "current_blocker_preserved": source_map_posture.get("authorization_status")
        == CURRENT_BLOCKER
        and source_map_posture.get("full_source_map_semantic_closure_authorized")
        is False,
        "blocker_reason_preserved": source_map_posture.get("not_authorized_reason")
        == BLOCKER_REASON,
        "project_axioms_empty": lean_posture.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and lean_posture.get("project_axiom_count") == 0,
        "lean_audit_no_axioms_preserved": lean_posture.get("parsed_axioms")
        == LEAN_AXIOMS_USED
        and lean_posture.get("depends_on_no_axioms") is True,
        "real_source_map_authorization_blocker_preserved": result_review.get(
            "tranche_004_audit_result_review_classification"
        )
        == "real_source_map_authorization_blocker_accepted_pending_remediation_planning",
        "required_witness_chain_evidence_defined": len(REQUIRED_WITNESS_CHAIN_EVIDENCE)
        == 10
        and REQUIRED_WITNESS_CHAIN_EVIDENCE[-1] == "qft_gr_source_map_closure_witness",
        "required_source_map_semantic_closure_evidence_defined": len(
            REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_EVIDENCE
        )
        >= 5,
        "authorization_conditions_defined": len(AUTHORIZATION_CONDITIONS) >= 6,
        "failure_conditions_defined": len(FAILURE_CONDITIONS) >= 6,
        "documentation_role_bounded": documentation_role[
            "documentation_alone_can_clear_blocker"
        ]
        is False,
        "lean_theorem_work_requirement_defined": lean_theorem_work_requirement[
            "lean_theorem_work_executed_by_this_packet"
        ]
        is False,
        "expert_re_review_requirement_defined": expert_re_review_requirement[
            "expert_re_review_required"
        ]
        is True
        and expert_re_review_requirement["expert_re_review_executed_by_this_packet"]
        is False,
        "packet_prepares_without_source_map_closure": forbidden_effect_status[
            "source_map_closure_claimed"
        ]
        is False
        and forbidden_effect_status["source_map_semantic_closure_authorized"] is False
        and forbidden_effect_status["witness_chain_constructed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"]
        is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_remediation_packet_result",
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
        else (
            "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
            "REMEDIATION_PACKET_BLOCKED"
        ),
        "consumes_audit_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_audit_result_review_pointer": _ptr(result_review_path),
        "consumed_audit_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_ONLY_"
            "NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "real_source_map_authorization_blocker_pending_remediation_packet_result_review"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "required_remediation_type": REQUIRED_REMEDIATION_TYPE,
        "current_blocker": CURRENT_BLOCKER,
        "blocker_reason": BLOCKER_REASON,
        "source_map_authorization_status": source_map_posture,
        "lean_audit_result": {
            "parsed_axioms": lean_posture.get("parsed_axioms"),
            "project_axioms_used": lean_posture.get("project_axioms_used"),
            "project_axiom_count": lean_posture.get("project_axiom_count"),
            "depends_on_no_axioms": lean_posture.get("depends_on_no_axioms"),
            "classification": lean_posture.get("classification"),
        },
        "project_axioms_used": PROJECT_AXIOMS_USED,
        "source_map_authorization_remediation_packet_prepared": accepted,
        "planning_scope": planning_scope,
        "required_witness_chain_evidence": REQUIRED_WITNESS_CHAIN_EVIDENCE,
        "required_source_map_semantic_closure_evidence": (
            REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_EVIDENCE
        ),
        "authorization_conditions": AUTHORIZATION_CONDITIONS,
        "failure_conditions": FAILURE_CONDITIONS,
        "documentation_role": documentation_role,
        "lean_theorem_work_requirement": lean_theorem_work_requirement,
        "expert_re_review_requirement": expert_re_review_requirement,
        "post_packet_review_target": NEXT_TARGET,
        "post_remediation_adjudication_target": POST_REMEDIATION_ADJUDICATION_TARGET,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": result_review.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": result_review.get(
            "other_release_blocking_obligation_count", 0
        ),
        "source_map_closure_claimed": False,
        "source_map_semantic_closure_authorized": False,
        "witness_chain_constructed": False,
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "broader_remediation_executed": False,
        "documentation_prepared": False,
        "policy_adjudication_executed": False,
        "expert_re_review_executed": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_"
            "AUTHORIZATION_REMEDIATION_PACKET"
        ),
        "selected_next_target_kind": "tranche_004_source_map_authorization_remediation_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_ONLY_"
            "NO_REMEDIATION_EXECUTION_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The remediation packet must be reviewed before any branch is selected.",
            },
            {
                "target": (
                    "execute_v01_alpha_dependency_remediation_tranche_004_bounded_source_map_"
                    "witness_chain_evidence_construction"
                ),
                "decision": "deferred",
                "reason": "Evidence construction must be authorized by packet result review first.",
            },
            {
                "target": (
                    "prepare_v01_alpha_dependency_remediation_tranche_004_documentation_only_"
                    "retained_blocker_packet"
                ),
                "decision": "deferred",
                "reason": "A documentation-only path cannot clear the blocker and must be selected explicitly after review.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_blocker_declaration_packet",
                "decision": "deferred",
                "reason": "Fail-closed release-readiness blocker declaration is a possible branch, not selected by this preparation packet.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 004 source-map authorization "
            "remediation packet prepares only the evidence/remediation plan for the retained "
            "source-map authorization blocker. It preserves full_source_map_semantic_closure_"
            "not_authorized, preserves the absent witness-chain reason, preserves project_"
            "axioms_used = [], and does not claim source-map closure, construct the witness "
            "chain, execute remediation, move tranche 004, assemble release, mark readiness, "
            "discharge theorem/proof debt, authorize Phase 2, close seams, validate empirically, "
            "promote the master action, or make an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 004 source-map "
            "authorization remediation packet."
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
        "v01_alpha_dependency_remediation_tranche_004_source_map_authorization_remediation_packet_report: "
        f"accepted={payload['accepted']} current_blocker={payload['current_blocker']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
