from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_report import (
    CANDIDATE_BLOCKER_STATUS,
    CURRENT_BLOCKER_STATUS,
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    POLICY_CLASSIFICATION,
    PROJECT_AXIOMS_USED,
    PROPOSED_MOVEMENT,
    PROPOSED_MOVEMENT_TOKEN,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    STATUS_CANDIDATE,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PROPOSED_MOVEMENT_AND_AUTHORIZES_REGISTRATION_EXECUTION_ONLY"
)

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result"
)
RESULT_REVIEW_CLASSIFICATION = (
    "proposed_blocker_movement_accepted_pending_registration_execution"
)
NEXT_TARGET = "execute_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration"

FORBIDDEN_EFFECTS = [
    "blocker_movement_registered",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "remediation_closure_executed",
    "remediation_executed",
    "broader_remediation_executed",
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


def _accepted_evidence(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("accepted_lean_dependency_evidence", {}))


def _documentation_surface(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("documentation_surface", {}))


def _movement_proposal(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("movement_proposal", {}))


def _retained_tranche_004(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("retained_tranche_004_carry_forward", {}))


def _tranche_006(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("tranche_006_obligation_carry_forward", {}))


def _release_blockers(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("release_blocking_obligations_carry_forward", []))


def _other_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("other_release_blocking_obligations", []))


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows]
        == [TRANCHE_004_FINDING_ID, SELECTED_FINDING_ID, TRANCHE_006_FINDING_ID]
        and rows[0].get("status_carry_forward") == TRANCHE_004_STATUS
        and rows[1].get("status_carry_forward")
        == "pending_result_review_policy_acceptable_with_documentation_requirement"
        and rows[2].get("status_carry_forward") == TRANCHE_006_STATUS
    )


def _other_obligations_carried_forward(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 2
        and [row.get("dependency_finding_id") for row in rows]
        == [TRANCHE_004_FINDING_ID, TRANCHE_006_FINDING_ID]
        and all(
            row.get("modified_by_tranche_005_policy_adjudication") is False
            for row in rows
        )
    )


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    evidence = _accepted_evidence(packet)
    documentation_surface = _documentation_surface(packet)
    movement_proposal = _movement_proposal(packet)
    retained_tranche_004 = _retained_tranche_004(packet)
    tranche_006 = _tranche_006(packet)
    release_blockers = _release_blockers(packet)
    other_obligations = _other_obligations(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_registration_packet": packet.get("packet_id")
        == EXPECTED_PACKET_ID,
        "registration_packet_accepted": packet.get("accepted") is True,
        "registration_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "registration_packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "selected_tranche_expected": packet.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": packet.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": packet.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": packet.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": packet.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET
        and packet.get("lean_audit_target", {}).get("command") == LEAN_AUDIT_COMMAND,
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": packet.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": packet.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "tranche_004_retained_blocker_preserved": packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "tranche_006_tracked_unresolved": packet.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and tranche_006.get("dependency") == TRANCHE_006_DEPENDENCY,
        "proposed_movement_exact": movement_proposal.get("current_status")
        == CURRENT_BLOCKER_STATUS
        and movement_proposal.get("candidate_status") == CANDIDATE_BLOCKER_STATUS
        and movement_proposal.get("proposed_movement") == PROPOSED_MOVEMENT
        and movement_proposal.get("proposed_movement_token") == PROPOSED_MOVEMENT_TOKEN,
        "movement_scope_tranche_005_only": movement_proposal.get("movement_scope")
        == "tranche_005_only"
        and movement_proposal.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and movement_proposal.get("selected_dependency") == SELECTED_DEPENDENCY,
        "movement_packet_did_not_register_movement": packet.get("blocker_movement_registered")
        is False
        and movement_proposal.get("registers_movement_now") is False
        and movement_proposal.get("clears_blocker_now") is False,
        "status_candidate_preserved": packet.get("status_candidate_reviewed")
        == STATUS_CANDIDATE
        and movement_proposal.get("accepted_status_candidate") == STATUS_CANDIDATE,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": packet.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_chain_preserved": packet.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
        and packet.get("documentation_accepted_only_as_documentation") is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "registration_packet_prepared_only": packet.get(
            "blocker_movement_registration_packet_prepared"
        )
        is True
        and packet.get("blocker_movement_registration_execution_authorized") is False
        and packet.get("blocker_movement_registered") is False,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_obligations_carried_forward": _other_obligations_carried_forward(
            other_obligations
        ),
        "authorizes_registration_execution_only": True,
        "does_not_register_movement_during_review": forbidden_effect_status[
            "blocker_movement_registered"
        ]
        is False,
        "does_not_clear_or_move_blocker": forbidden_effect_status["blocker_fully_remediated"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "does_not_move_tranche_004": forbidden_effect_status[
            "tranche_004_moved_to_documented_dependency_nonblocking"
        ]
        is False
        and forbidden_effect_status["tranche_004_retained_blocker_discharged"] is False,
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
        == "execute_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_packet": EXPECTED_PACKET_ID,
        "consumes_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_ONLY_"
            "AUTHORIZE_REGISTRATION_EXECUTION_NO_LIVE_BLOCKER_MOVEMENT"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_obligation_carry_forward": tranche_006,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": packet.get("lean_audit_target"),
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
        "policy_classification": POLICY_CLASSIFICATION,
        "documentation_result_review_classification": DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
        "documentation_surface": documentation_surface,
        "documentation_accepted_only_as_documentation": True,
        "status_candidate_reviewed": STATUS_CANDIDATE,
        "proposed_movement_accepted": accepted,
        "movement_proposal": {
            "selected_tranche_id": movement_proposal.get("selected_tranche_id"),
            "selected_remediation_finding_id": movement_proposal.get(
                "selected_remediation_finding_id"
            ),
            "selected_dependency": movement_proposal.get("selected_dependency"),
            "current_status": movement_proposal.get("current_status"),
            "candidate_status": movement_proposal.get("candidate_status"),
            "accepted_status_candidate": movement_proposal.get("accepted_status_candidate"),
            "proposed_movement": movement_proposal.get("proposed_movement"),
            "proposed_movement_token": movement_proposal.get("proposed_movement_token"),
            "movement_scope": movement_proposal.get("movement_scope"),
            "tranche_001_status": movement_proposal.get("tranche_001_status"),
            "tranche_002_status": movement_proposal.get("tranche_002_status"),
            "tranche_003_status": movement_proposal.get("tranche_003_status"),
            "tranche_004_status": movement_proposal.get("tranche_004_status"),
            "tranche_006_status": movement_proposal.get("tranche_006_status"),
            "requires_result_review_before_execution": movement_proposal.get(
                "requires_result_review_before_execution"
            ),
            "registers_movement_now": False,
            "clears_blocker_now": False,
            "marks_release_readiness_now": False,
        },
        "blocker_movement_registration_packet_result_review_classification": (
            RESULT_REVIEW_CLASSIFICATION
        ),
        "blocker_movement_registration_packet_prepared": True,
        "blocker_movement_registration_execution_authorized": accepted,
        "blocker_movement_registered": False,
        "blocker_movement_authorized": False,
        "remediation_closure_authorized": False,
        "remediation_fully_satisfied": False,
        "tranche_005_release_blocker_status": (
            "release_blocking_pending_blocker_movement_registration_execution"
        ),
        "global_release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "blocker_movement_registration_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_ONLY_NO_RELEASE_PROMOTION_OR_GLOBAL_DEBT_DISCHARGE"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The proposed movement is accepted for bounded registration execution only.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_005_movement",
                "decision": "deferred",
                "reason": "Next-tranche selection requires movement registration execution and result review first.",
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "Release-readiness adjudication remains blocked by retained tranche 004 and "
                    "tracked tranche 006."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 005 blocker movement registration "
            "packet result review accepts the proposed movement and authorizes only bounded "
            "registration execution. It does not register blocker movement, clear tranche 005, "
            "move retained tranche 004, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge Lean theorem debt, reduce axiom/spec-backed proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 005 blocker movement "
            "registration packet result review."
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
        "v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
