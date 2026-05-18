from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_RESULT_REVIEW_ACCEPTS_EXACT_"
    "LEAN_DEPENDENCY_EVIDENCE_AND_AUTHORIZES_RELEASE_POLICY_ADJUDICATION_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_AUDIT_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_v0"
EXPECTED_AUDIT_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_EXECUTED_FOR_"
    "FINITE_TRANSPORT_THEOREMS_CONSTRUCT_RESIDUAL_PACKAGE_WITH_NO_REMEDIATION_OR_RELEASE_PROMOTION"
)
EXPECTED_AUDIT_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_003_audit_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-003"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-003"
SELECTED_DEPENDENCY = "finite_transport_theorems_construct_residual_package_v0"
SELECTED_DEPENDENCY_CLASS = "lean_bridge_dependency"
LEAN_TARGET = (
    "ToeFormal.Bridges.QMSTATTransportResidualPackage."
    "finite_transport_theorems_construct_residual_package_v0"
)
LEAN_SOURCE = "formal/toe_formal/ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PROJECT_AXIOMS_USED: list[str] = []
TRANCHE_CLASSIFICATION = "audit_evidence_accepted_pending_release_policy_adjudication"
NEXT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_003_release_policy_adjudication_packet"
)

FORBIDDEN_EFFECTS = [
    "remediation_closure_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "release_policy_adjudication_executed",
    "release_policy_decision_made",
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


def _lean_evidence(audit: dict[str, Any]) -> dict[str, Any]:
    return dict(audit.get("lean_evidence", {}))


def _release_blockers(audit: dict[str, Any]) -> list[dict[str, Any]]:
    return list(audit.get("release_blocking_obligations_carry_forward", []))


def _other_blockers(audit: dict[str, Any]) -> list[dict[str, Any]]:
    return list(audit.get("other_release_blocking_obligations", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 4
        and [row.get("dependency_finding_id") for row in rows]
        == [
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-004",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ]
    )


def _other_blockers_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
            for row in rows
        )
    )


def build_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    evidence = _lean_evidence(audit)
    release_blockers = _release_blockers(audit)
    other_blockers = _other_blockers(audit)
    selected_obligation = _selected_obligation(release_blockers)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_audit": audit.get("audit_id") == EXPECTED_AUDIT_ID,
        "audit_accepted": audit.get("accepted") is True,
        "audit_executed": audit.get("executed") is True,
        "audit_outcome_expected": audit.get("outcome_id") == EXPECTED_AUDIT_OUTCOME,
        "audit_selected_this_review": audit.get("selected_next_target")
        == EXPECTED_AUDIT_SELECTED_TARGET,
        "selected_tranche_expected": audit.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": audit.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": audit.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": audit.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_expected": evidence.get("lean_target") == LEAN_TARGET
        and evidence.get("lean_source") == LEAN_SOURCE,
        "exact_lean_dependency_evidence_matches": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS,
        "standard_lean_axioms_preserved": evidence.get("standard_lean_axioms_used")
        == EXPECTED_AXIOMS
        and evidence.get("standard_lean_or_mathlib_axioms_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axiom_count") == len(EXPECTED_AXIOMS),
        "project_axioms_empty": evidence.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0
        and evidence.get("project_local_axioms_present") is False,
        "audit_claims_no_debt_discharge": evidence.get(
            "theorem_debt_discharged_by_this_audit"
        )
        is False
        and evidence.get("proof_debt_reduced_by_this_audit") is False
        and evidence.get("retained_assumptions_discharged_by_this_audit") is False,
        "tranche_001_documented_nonblocking_preserved": audit.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": audit.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_blockers_unmodified": _other_blockers_unmodified(other_blockers),
        "classification_is_conservative": TRANCHE_CLASSIFICATION
        == "audit_evidence_accepted_pending_release_policy_adjudication",
        "no_remediation_closure": forbidden_effect_status["remediation_closure_executed"]
        is False
        and forbidden_effect_status["broader_remediation_executed"] is False,
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
        == "prepare_v01_alpha_dependency_remediation_tranche_003_release_policy_adjudication_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_RESULT_REVIEW_BLOCKED",
        "consumes_audit": EXPECTED_AUDIT_ID,
        "consumes_audit_pointer": _ptr(audit_path),
        "consumed_audit_schema_id": audit.get("schema_id"),
        "source_execution_packet_result_review": audit.get(
            "consumes_tranche_003_execution_packet_result_review"
        ),
        "review_scope": (
            "REVIEW_TRANCHE_003_AUDIT_RESULT_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "lean_audit_target": {
            "lean_target": evidence.get("lean_target"),
            "lean_source": evidence.get("lean_source"),
            "command": evidence.get("command"),
            "command_context": evidence.get("command_context"),
            "exit_code": evidence.get("exit_code"),
        },
        "exact_lean_dependency_evidence": {
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
        "tranche_003_audit_result_classification": TRANCHE_CLASSIFICATION,
        "classification_options_considered": [
            "audit_evidence_accepted",
            "audit_evidence_insufficient_requires_reaudit",
            "audit_evidence_policy_sensitive_requires_adjudication",
            "audit_evidence_failed_requires_redesign",
            TRANCHE_CLASSIFICATION,
        ],
        "classification_reason": (
            "Exact Lean dependency evidence was captured for "
            "finite_transport_theorems_construct_residual_package_v0 and no project-local "
            "axioms were found. The evidence is accepted, but standard Lean axiom acceptability "
            "must be prepared for v0.1-alpha release-policy adjudication before any blocker "
            "movement or remediation closure."
        ),
        "audit_evidence_accepted": accepted,
        "release_policy_adjudication_packet_preparation_authorized": accepted,
        "release_policy_adjudication_executed": False,
        "release_policy_decision_made": False,
        "tranche_003_release_blocker_status": (
            "still_blocking_pending_release_policy_adjudication_packet_preparation"
        ),
        "remediation_closure_authorized": False,
        "remediation_closure_executed": False,
        "broader_remediation_executed": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_AUDIT_RESULT_REVIEW",
        "selected_next_target_kind": "tranche_003_release_policy_adjudication_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Accepted standard Lean axiom evidence requires a prepared v0.1-alpha "
                    "release-policy adjudication packet before blocker movement can be considered."
                ),
            },
            {
                "target": (
                    "execute_v01_alpha_dependency_remediation_tranche_003_release_policy_"
                    "adjudication"
                ),
                "decision": "deferred",
                "reason": "Policy adjudication execution requires packet preparation and result review first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tranche 003 policy work and the remaining tracked obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 003 audit result review accepts exact "
            "Lean dependency evidence for finite_transport_theorems_construct_residual_package_v0 "
            "and authorizes only release-policy adjudication packet preparation. It does not "
            "decide release policy, close remediation, move blockers, assemble the release packet, "
            "mark v0.1-alpha readiness, discharge theorem/proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(audit_path=audit_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation tranche 003 audit result review."
    )
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        audit_path=audit_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_003_audit_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
