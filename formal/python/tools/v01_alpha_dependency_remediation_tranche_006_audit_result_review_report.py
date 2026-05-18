from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_audit_report import (
    AUDIT_ID as EXPECTED_AUDIT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_SOURCE,
    LEAN_TARGET,
    OUTCOME_ID as EXPECTED_AUDIT_OUTCOME,
    PROJECT_AXIOMS_USED,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    TRANCHE_006_SOURCE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_ACCEPTS_EXACT_"
    "LEAN_DEPENDENCY_EVIDENCE_AND_AUTHORIZES_RELEASE_POLICY_ADJUDICATION_PACKET_"
    "PREPARATION_ONLY"
)

DEFAULT_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_AUDIT_SELECTED_TARGET = "review_v01_alpha_dependency_remediation_tranche_006_audit_result"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
TRANCHE_CLASSIFICATION = "audit_evidence_accepted_pending_release_policy_adjudication"
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet"

FORBIDDEN_EFFECTS = [
    "remediation_closure_executed",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "release_policy_adjudication_executed",
    "release_policy_decision_made",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "tranche_006_moved_or_cleared",
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


def _lean_evidence(audit: dict[str, Any]) -> dict[str, Any]:
    return dict(audit.get("lean_evidence", {}))


def _remaining_obligations(audit: dict[str, Any]) -> list[dict[str, Any]]:
    return list(audit.get("remaining_release_blocking_obligations", []))


def _selected_obligation(audit: dict[str, Any]) -> dict[str, Any]:
    selected = dict(audit.get("selected_release_blocking_obligation", {}))
    if selected:
        return selected
    for row in _remaining_obligations(audit):
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _retained_tranche_004(audit: dict[str, Any]) -> dict[str, Any]:
    return dict(audit.get("retained_tranche_004_carry_forward", {}))


def _review_release_blocking_obligations(
    *,
    selected_obligation: dict[str, Any],
    retained_tranche_004: dict[str, Any],
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
            "modified_by_tranche_006_audit_result_review": False,
        },
        {
            "dependency_finding_id": SELECTED_FINDING_ID,
            "dependency": selected_obligation.get("dependency", SELECTED_DEPENDENCY),
            "dependency_class": selected_obligation.get(
                "dependency_class", SELECTED_DEPENDENCY_CLASS
            ),
            "status_carry_forward": (
                "release_blocking_pending_tranche_006_release_policy_adjudication_packet_preparation"
            ),
            "modified_by_tranche_006_audit_result_review": False,
        },
    ]


def _other_release_blocking_obligations(
    *,
    retained_tranche_004: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "dependency_finding_id": TRANCHE_004_FINDING_ID,
            "dependency": retained_tranche_004.get("dependency", TRANCHE_004_DEPENDENCY),
            "dependency_class": retained_tranche_004.get(
                "dependency_class", "blocked_bridge_authorization_dependency"
            ),
            "status_carry_forward": TRANCHE_004_STATUS,
            "modified_by_tranche_006_audit_result_review": False,
        }
    ]


def build_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    evidence = _lean_evidence(audit)
    selected_obligation = _selected_obligation(audit)
    retained_tranche_004 = _retained_tranche_004(audit)
    review_release_blockers = _review_release_blocking_obligations(
        selected_obligation=selected_obligation,
        retained_tranche_004=retained_tranche_004,
    )
    other_blockers = _other_release_blocking_obligations(
        retained_tranche_004=retained_tranche_004,
    )
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
        and evidence.get("lean_source") == LEAN_SOURCE
        and evidence.get("command") == LEAN_AUDIT_COMMAND,
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
        "tranche_003_documented_nonblocking_preserved": audit.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": audit.get("tranche_005_status")
        == TRANCHE_005_STATUS
        and audit.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_004_retained_blocker_preserved": audit.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "release_blockers_remain_tracked": [
            row.get("dependency_finding_id") for row in review_release_blockers
        ]
        == [TRANCHE_004_FINDING_ID, SELECTED_FINDING_ID],
        "other_blockers_unmodified": len(other_blockers) == 1
        and other_blockers[0].get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and other_blockers[0].get("modified_by_tranche_006_audit_result_review")
        is False,
        "classification_is_conservative": TRANCHE_CLASSIFICATION
        == "audit_evidence_accepted_pending_release_policy_adjudication",
        "tranche_006_not_moved": selected_obligation.get(
            "status_carry_forward"
        )
        != "documented_dependency_nonblocking",
        "no_remediation_closure": forbidden_effect_status["remediation_closure_executed"]
        is False
        and forbidden_effect_status["broader_remediation_executed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["tranche_006_moved_or_cleared"] is False,
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
        == "prepare_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_BLOCKED",
        "consumes_audit": EXPECTED_AUDIT_ID,
        "consumes_audit_pointer": _ptr(audit_path),
        "consumed_audit_schema_id": audit.get("schema_id"),
        "source_execution_packet_result_review": audit.get(
            "consumes_tranche_006_execution_packet_result_review"
        ),
        "review_scope": (
            "REVIEW_TRANCHE_006_AUDIT_RESULT_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_tranche_004_release_blocker_carry_forward_required": True,
        "release_readiness_blocked_by_tranche_004": True,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "global_release_readiness_still_blocked": True,
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
        "tranche_006_audit_result_classification": TRANCHE_CLASSIFICATION,
        "classification_options_considered": [
            "audit_evidence_accepted",
            "audit_evidence_insufficient_requires_reaudit",
            "audit_evidence_policy_sensitive_requires_adjudication",
            "audit_evidence_failed_requires_redesign",
            "semantic_authorization_blocker_detected",
            TRANCHE_CLASSIFICATION,
        ],
        "classification_reason": (
            "Exact Lean dependency evidence was captured for "
            "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0 and no "
            "project-local axioms were found. The evidence is accepted, but standard Lean "
            "axiom acceptability must be prepared for v0.1-alpha release-policy adjudication "
            "before any tranche 006 blocker movement or remediation closure."
        ),
        "audit_evidence_accepted": accepted,
        "release_policy_adjudication_packet_preparation_authorized": accepted,
        "release_policy_adjudication_executed": False,
        "release_policy_decision_made": False,
        "tranche_006_release_blocker_status": (
            "still_blocking_pending_release_policy_adjudication_packet_preparation"
        ),
        "remediation_closure_authorized": False,
        "remediation_closure_executed": False,
        "remediation_executed": False,
        "broader_remediation_executed": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
        "tranche_006_moved_or_cleared": False,
        "release_blocking_obligations_carry_forward": review_release_blockers,
        "release_blocking_obligation_count": len(review_release_blockers),
        "other_release_blocking_obligations": other_blockers,
        "other_release_blocking_obligation_count": len(other_blockers),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW",
        "selected_next_target_kind": (
            "tranche_006_release_policy_adjudication_packet_preparation_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Accepted standard Lean axiom evidence requires a prepared v0.1-alpha "
                    "release-policy adjudication packet before tranche 006 blocker movement "
                    "can be considered."
                ),
            },
            {
                "target": (
                    "execute_v01_alpha_dependency_remediation_tranche_006_release_policy_"
                    "adjudication"
                ),
                "decision": "deferred",
                "reason": "Policy adjudication execution requires packet preparation and result review first.",
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "Release readiness remains blocked by retained tranche 004, but the "
                    "bounded tranche 006 remediation queue can continue."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 006 audit result review accepts exact "
            "Lean dependency evidence for supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0 "
            "and authorizes only release-policy adjudication packet preparation. It carries "
            "tranche 004 as retained/release-blocking and preserves tranches 001, 002, 003, "
            "and 005 as documented/nonblocking. It does not decide release policy, close "
            "remediation, move blockers, assemble the release packet, mark v0.1-alpha "
            "readiness, discharge theorem/proof debt, discharge retained assumptions, authorize "
            "Phase 2, close seams, validate empirically, promote the master action, promote "
            "claims, or make an external-truth claim."
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
        description="Generate the v0.1-alpha dependency remediation tranche 006 audit result review."
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
        "v01_alpha_dependency_remediation_tranche_006_audit_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
