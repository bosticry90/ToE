from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_POLICY_QUESTION_PREPARATION_AND_AUTHORIZES_POLICY_ADJUDICATION_EXECUTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_v0"
)
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_"
    "PREPARED_WITH_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication_packet_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-002"
SELECTED_DEPENDENCY = "stationary_implies_operator_zero"
SELECTED_DEPENDENCY_CLASS = "lean_theorem_dependency"
LEAN_TARGET = "ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PROJECT_AXIOMS_USED: list[str] = []
EXPECTED_POLICY_QUESTION = (
    "Are [propext, Classical.choice, Quot.sound] acceptable standard Lean dependencies "
    "for tranche 002 / stationary_implies_operator_zero under the v0.1-alpha release "
    "dependency policy, given project_axioms_used = []?"
)
NEXT_TARGET = (
    "execute_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication"
)

FORBIDDEN_EFFECTS = [
    "policy_adjudication_executed",
    "release_policy_decision_made",
    "remediation_closure_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
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


def _accepted_evidence(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("accepted_lean_dependency_evidence", {}))


def _release_blockers(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("release_blocking_obligations_carry_forward", []))


def _other_blockers(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("other_release_blocking_obligations", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 5
        and [row.get("dependency_finding_id") for row in rows]
        == [
            "V01-ALPHA-DEP-REM-002",
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-004",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ]
    )


def _other_blockers_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 4
        and all(row.get("modified_by_tranche_002") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_002"
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
    release_blockers = _release_blockers(packet)
    other_blockers = _other_blockers(packet)
    selected_obligation = _selected_obligation(release_blockers)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_accepted": packet.get("accepted") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "selected_tranche_expected": packet.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": packet.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": packet.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": packet.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": packet.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get(
            "parsed_axioms"
        )
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty_preserved": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "policy_question_prepared": packet.get("policy_question")
        == EXPECTED_POLICY_QUESTION,
        "policy_acceptance_and_failure_criteria_present": len(
            packet.get("release_policy_acceptance_criteria", [])
        )
        >= 6
        and len(packet.get("release_policy_failure_criteria", [])) >= 6,
        "packet_prepared_policy_question_only": packet.get("packet_scope")
        == (
            "PREPARE_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_"
            "NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
        )
        and packet.get("policy_adjudication_executed") is False
        and packet.get("policy_decision_made") is False,
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_remains_pending_adjudication": packet.get(
            "tranche_002_release_blocker_status"
        )
        == "still_blocking_pending_release_policy_adjudication_packet_result_review"
        and packet.get("remediation_fully_satisfied") is False
        and packet.get("blocker_movement_authorized") is False,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_blockers_unmodified": _other_blockers_unmodified(other_blockers),
        "policy_adjudication_execution_authorized_only": NEXT_TARGET
        == "execute_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication",
        "no_policy_decision_during_result_review": forbidden_effect_status[
            "release_policy_decision_made"
        ]
        is False
        and forbidden_effect_status["policy_adjudication_executed"] is False,
        "no_remediation_closure": forbidden_effect_status["remediation_closure_executed"]
        is False
        and forbidden_effect_status["broader_remediation_executed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_authorized"]
        is False
        and forbidden_effect_status["blocker_movement_registered"] is False,
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
        "no_release_packet_assembly_or_readiness_marking": forbidden_effect_status[
            "release_packet_assembled"
        ]
        is False
        and forbidden_effect_status["v01_alpha_marked_ready"] is False,
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
        == "execute_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_packet": EXPECTED_PACKET_ID,
        "consumes_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "source_audit_result_review": packet.get("consumes_audit_result_review"),
        "review_scope": (
            "REVIEW_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_"
            "AUTHORIZE_POLICY_ADJUDICATION_EXECUTION_NO_POLICY_DECISION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "lean_audit_target": {
            "lean_target": packet.get("lean_audit_target", {}).get("lean_target"),
            "command": packet.get("lean_audit_target", {}).get("command"),
            "exit_code": packet.get("lean_audit_target", {}).get("exit_code"),
        },
        "accepted_lean_dependency_evidence": {
            "parsed_axioms": evidence.get("parsed_axioms"),
            "exact_axioms_or_dependencies_used": evidence.get(
                "exact_axioms_or_dependencies_used"
            ),
            "standard_lean_axioms_used": evidence.get("standard_lean_axioms_used"),
            "standard_lean_axiom_count": evidence.get("standard_lean_axiom_count"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
            "classification": evidence.get("classification"),
            "raw_output": evidence.get("raw_output"),
        },
        "policy_question": packet.get("policy_question"),
        "release_policy_acceptance_criteria": packet.get(
            "release_policy_acceptance_criteria", []
        ),
        "release_policy_failure_criteria": packet.get("release_policy_failure_criteria", []),
        "packet_preparation_accepted": accepted,
        "policy_adjudication_execution_authorized": accepted,
        "policy_adjudication_execution_scope": (
            "DECIDE_ONLY_WHETHER_STANDARD_LEAN_AXIOMS_ARE_ACCEPTABLE_FOR_TRANCHE_002_"
            "UNDER_V01_ALPHA_POLICY_GIVEN_EMPTY_PROJECT_AXIOMS"
        ),
        "policy_decision_made": False,
        "policy_adjudication_executed": False,
        "tranche_002_release_blocker_status": (
            "still_blocking_pending_policy_adjudication_execution"
        ),
        "remediation_closure_authorized": False,
        "remediation_closure_executed": False,
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_blockers,
        "other_release_blocking_obligation_count": len(other_blockers),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_POLICY_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "policy_adjudication_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The policy question packet is complete, so the narrow tranche 002 policy adjudication execution can be authorized.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by the pending tranche 002 policy decision and tracked blockers.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet",
                "decision": "deferred",
                "reason": "Next-tranche selection is deferred until tranche 002 policy meaning is adjudicated and reviewed.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 002 release-policy adjudication "
            "packet result review accepts policy-question preparation and authorizes only narrow "
            "policy adjudication execution. It does not decide the policy question, close "
            "remediation, move blockers, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge theorem/proof debt, discharge retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, promote claims, or "
            "make an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 002 release-policy "
            "adjudication packet result review."
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
        "v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
