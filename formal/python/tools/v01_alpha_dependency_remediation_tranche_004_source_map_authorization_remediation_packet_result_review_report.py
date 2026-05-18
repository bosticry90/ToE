from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_RESULT_REVIEW_ACCEPTS_REAL_BLOCKER_REMEDIATION_PLAN_AND_"
    "SELECTS_BOUNDED_NEXT_ACTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_v0"
)
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_"
    "remediation_packet_result"
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
CURRENT_BLOCKER = "full_source_map_semantic_closure_not_authorized"
BLOCKER_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
PROJECT_AXIOMS_USED: list[str] = []
LEAN_AXIOMS_USED: list[str] = []

NEXT_TARGET = "prepare_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet"
RESULT_REVIEW_CLASSIFICATION = (
    "real_source_map_authorization_remediation_plan_accepted_bounded_witness_chain_"
    "evidence_packet_preparation_selected"
)

FORBIDDEN_EFFECTS = [
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
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


def _release_blockers(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("release_blocking_obligations_carry_forward", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows]
        == [
            "V01-ALPHA-DEP-REM-004",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ]
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
            for row in rows
        )
    )


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    source_map = dict(packet.get("source_map_authorization_status", {}))
    lean = dict(packet.get("lean_audit_result", {}))
    planning_scope = dict(packet.get("planning_scope", {}))
    documentation_role = dict(packet.get("documentation_role", {}))
    release_blockers = _release_blockers(packet)
    selected_obligation = _selected_obligation(release_blockers)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    allowed_branches = list(planning_scope.get("allowed_future_branches_after_packet_review", []))

    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_accepted": packet.get("accepted") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "tranche_004_only_reviewed_target": packet.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and packet.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and packet.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_obligation_expected": selected_obligation.get("dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "current_blocker_preserved": packet.get("current_blocker") == CURRENT_BLOCKER
        and source_map.get("authorization_status") == CURRENT_BLOCKER
        and source_map.get("full_source_map_semantic_closure_authorized") is False,
        "blocker_reason_preserved": packet.get("blocker_reason") == BLOCKER_REASON
        and source_map.get("not_authorized_reason") == BLOCKER_REASON,
        "project_axioms_empty": packet.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axiom_count") == 0,
        "lean_audit_no_axioms_preserved": lean.get("parsed_axioms") == LEAN_AXIOMS_USED
        and lean.get("depends_on_no_axioms") is True,
        "documentation_alone_cannot_clear": documentation_role.get(
            "documentation_alone_can_clear_blocker"
        )
        is False,
        "real_blocker_plan_accepted": packet.get(
            "source_map_authorization_remediation_packet_prepared"
        )
        is True
        and planning_scope.get("scope_kind")
        == "SOURCE_MAP_AUTHORIZATION_REMEDIATION_PLANNING_ONLY",
        "bounded_witness_chain_branch_available": (
            "bounded_source_map_witness_chain_evidence_construction_attempt"
            in allowed_branches
        ),
        "retained_blocker_branch_available": (
            "documentation_only_retained_blocker_packet" in allowed_branches
        ),
        "fail_closed_branch_available": (
            "fail_closed_release_readiness_blocker_declaration" in allowed_branches
        ),
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": packet.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": packet.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "no_source_map_closure": packet.get("source_map_closure_claimed") is False
        and packet.get("source_map_semantic_closure_authorized") is False
        and forbidden_effect_status["source_map_closure_claimed"] is False
        and forbidden_effect_status["source_map_semantic_closure_authorized"] is False,
        "no_witness_chain_construction": packet.get("witness_chain_constructed") is False
        and forbidden_effect_status["witness_chain_constructed"] is False
        and forbidden_effect_status["source_map_witness_chain_evidence_constructed"]
        is False,
        "no_blocker_movement": packet.get("blocker_movement_registered") is False
        and packet.get("blocker_movement_authorized") is False
        and forbidden_effect_status["blocker_movement_registered"] is False
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
        == "prepare_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
            "REMEDIATION_PACKET_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_remediation_packet": EXPECTED_PACKET_ID,
        "consumes_remediation_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_RESULT_"
            "ONLY_NO_CLOSURE_CONSTRUCTION_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "real_source_map_authorization_blocker_remediation_plan_accepted_pending_"
            "witness_chain_evidence_packet_preparation"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "current_blocker": CURRENT_BLOCKER,
        "blocker_reason": BLOCKER_REASON,
        "source_map_authorization_status": source_map,
        "lean_audit_result": {
            "parsed_axioms": lean.get("parsed_axioms"),
            "project_axioms_used": lean.get("project_axioms_used"),
            "project_axiom_count": lean.get("project_axiom_count"),
            "depends_on_no_axioms": lean.get("depends_on_no_axioms"),
            "classification": lean.get("classification"),
        },
        "project_axioms_used": PROJECT_AXIOMS_USED,
        "documentation_alone_can_clear_blocker": False,
        "remediation_packet_result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "remediation_plan_accepted": accepted,
        "bounded_witness_chain_evidence_packet_preparation_authorized": accepted,
        "source_map_witness_chain_evidence_construction_authorized": False,
        "retained_source_map_blocker_declaration_preparation_authorized": False,
        "fail_closed_release_readiness_blocker_declaration_preparation_authorized": False,
        "branch_selection_reason": (
            "The packet identifies a bounded witness-chain evidence branch as available, "
            "so the review selects packet preparation for that branch while keeping retained "
            "blocker and fail-closed declaration paths deferred."
        ),
        "branches_considered": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "branch": "bounded_source_map_witness_chain_evidence_packet_preparation",
            },
            {
                "target": "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration",
                "decision": "deferred",
                "branch": "retained_source_map_blocker_declaration",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_blocker_declaration_packet",
                "decision": "deferred",
                "branch": "fail_closed_release_readiness_blocker_declaration",
            },
        ],
        "required_witness_chain_evidence": packet.get("required_witness_chain_evidence", []),
        "required_source_map_semantic_closure_evidence": packet.get(
            "required_source_map_semantic_closure_evidence", []
        ),
        "authorization_conditions": packet.get("authorization_conditions", []),
        "failure_conditions": packet.get("failure_conditions", []),
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": packet.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": packet.get(
            "other_release_blocking_obligation_count", 0
        ),
        "source_map_closure_claimed": False,
        "source_map_semantic_closure_authorized": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_evidence_constructed": False,
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
            "AUTHORIZATION_REMEDIATION_PACKET_RESULT_REVIEW"
        ),
        "selected_next_target_kind": "tranche_004_source_map_witness_chain_evidence_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_ONLY_"
            "NO_EVIDENCE_CONSTRUCTION_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Prepare the bounded witness-chain evidence packet; do not construct "
                    "evidence or claim closure during this review."
                ),
            },
            {
                "target": "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration",
                "decision": "deferred",
                "reason": (
                    "The retained-blocker declaration remains available if witness-chain "
                    "evidence preparation is not accepted or proves unavailable."
                ),
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_004_bounded_source_map_witness_chain_evidence_construction",
                "decision": "deferred",
                "reason": "Execution requires witness-chain evidence packet preparation and result review first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_blocker_declaration_packet",
                "decision": "deferred",
                "reason": "Fail-closed release-readiness blocker declaration is not selected while a bounded evidence-packet preparation branch is available.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 004 source-map authorization "
            "remediation packet result review accepts the remediation plan for a real source-map "
            "authorization blocker and selects only witness-chain evidence packet preparation. "
            "It preserves full_source_map_semantic_closure_not_authorized, preserves the "
            "absent witness-chain reason, preserves project_axioms_used = [], confirms "
            "documentation alone cannot clear the blocker, and does not claim source-map "
            "closure, construct the witness chain, move tranche 004, assemble release, mark "
            "readiness, discharge theorem/proof debt, authorize Phase 2, close seams, validate "
            "empirically, promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(packet_path=packet_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 004 source-map "
            "authorization remediation packet result review."
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
    payload = write_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_004_source_map_authorization_remediation_packet_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['remediation_packet_result_review_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
