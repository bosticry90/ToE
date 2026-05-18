from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_execution_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_SOURCE,
    LEAN_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    REQUIRED_REMEDIATION_TYPE,
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
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_"
    "20260515_v0"
)
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_LEAN_DEPENDENCY_AUDIT_SCOPE_AND_AUTHORIZES_TRANCHE_006_AUDIT_EXECUTION_ONLY"
)

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_006_execution_packet_result"
)
NEXT_TARGET = "execute_v01_alpha_dependency_remediation_tranche_006_audit"
RESULT_REVIEW_CLASSIFICATION = (
    "lean_dependency_audit_scope_accepted_tranche_006_audit_execution_authorized_only"
)

FORBIDDEN_EFFECTS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "lean_dependency_audit_executed",
    "lean_dependency_evidence_captured",
    "tranche_006_audit_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "expert_re_review_executed",
    "blocker_movement_authorized",
    "blocker_movement_registered",
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


def _remaining_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("remaining_release_blocking_obligations", []))


def _selectable_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("selectable_unresolved_obligations", []))


def _selected_obligation(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("selected_release_blocking_obligation", {}))


def _retained_tranche_004(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("retained_tranche_004_carry_forward", {}))


def _tranche_006(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("tranche_006_obligation_carry_forward", {}))


def _lean_audit_target(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("lean_dependency_audit_target", {}))


def _required_evidence_surface(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("required_evidence_surface", {}))


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    remaining_obligations = _remaining_obligations(packet)
    selectable_obligations = _selectable_obligations(packet)
    selected_obligation = _selected_obligation(packet)
    retained_tranche_004 = _retained_tranche_004(packet)
    tranche_006 = _tranche_006(packet)
    audit_target = _lean_audit_target(packet)
    required_evidence = _required_evidence_surface(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_execution_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "execution_packet_accepted": packet.get("accepted") is True,
        "execution_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "execution_packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": packet.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": packet.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": packet.get("tranche_005_status")
        == TRANCHE_005_STATUS
        and packet.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_004_retained_blocker_preserved": packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "tranche_006_only_selected_target": packet.get("selection_count") == 1
        and packet.get("selected_tranche_id") == SELECTED_TRANCHE_ID
        and packet.get("selected_remediation_finding_id") == SELECTED_FINDING_ID,
        "selected_dependency_expected": packet.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": packet.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "required_remediation_type_exact": packet.get("required_remediation_type")
        == REQUIRED_REMEDIATION_TYPE,
        "current_ledger_contains_retained_tranche_004_and_active_tranche_006": len(
            remaining_obligations
        )
        == 2
        and [row.get("dependency_finding_id") for row in remaining_obligations]
        == [TRANCHE_004_FINDING_ID, SELECTED_FINDING_ID]
        and remaining_obligations[0].get("status_carry_forward") == TRANCHE_004_STATUS
        and remaining_obligations[1].get("status_carry_forward")
        == TRANCHE_006_SOURCE_STATUS,
        "only_one_selectable_unresolved_obligation": len(selectable_obligations) == 1
        and selectable_obligations[0].get("dependency_finding_id") == SELECTED_FINDING_ID,
        "tranche_006_carry_forward_matches_selection": packet.get("tranche_006_status")
        == "selected_for_execution_packet_preparation"
        and tranche_006.get("dependency_finding_id") == SELECTED_FINDING_ID
        and tranche_006.get("dependency") == SELECTED_DEPENDENCY
        and tranche_006.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_exact": audit_target.get("lean_target") == LEAN_TARGET
        and audit_target.get("lean_source") == LEAN_SOURCE
        and audit_target.get("audit_command") == LEAN_AUDIT_COMMAND,
        "required_evidence_surface_exact": required_evidence.get("lean_target") == LEAN_TARGET
        and required_evidence.get("audit_command") == LEAN_AUDIT_COMMAND
        and required_evidence.get("execution_status") == "prepared_not_executed_v0",
        "no_audit_execution_in_packet_or_review": packet.get("lean_dependency_audit_executed")
        is False
        and packet.get("lean_dependency_evidence_captured") is False
        and packet.get("tranche_006_audit_executed") is False
        and audit_target.get("executed_by_this_packet") is False
        and forbidden_effect_status["lean_dependency_audit_executed"] is False
        and forbidden_effect_status["lean_dependency_evidence_captured"] is False
        and forbidden_effect_status["tranche_006_audit_executed"] is False,
        "no_remediation_execution": packet.get("remediation_executed") is False
        and packet.get("remediation_execution_authorized") is False
        and forbidden_effect_status["remediation_executed"] is False
        and forbidden_effect_status["remediation_execution_authorized"] is False,
        "no_documentation_or_policy_prepared": packet.get("documentation_prepared") is False
        and packet.get("policy_adjudication_executed") is False
        and forbidden_effect_status["documentation_prepared"] is False
        and forbidden_effect_status["policy_adjudication_executed"] is False,
        "no_blocker_movement": packet.get("blocker_movement_registered") is False
        and packet.get("blocker_movement_authorized") is False
        and packet.get("tranche_004_moved_to_documented_dependency_nonblocking") is False
        and packet.get("tranche_006_moved_or_cleared") is False
        and forbidden_effect_status["blocker_movement_registered"] is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["tranche_006_moved_or_cleared"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
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
        == "execute_v01_alpha_dependency_remediation_tranche_006_audit",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_tranche_006_execution_packet": EXPECTED_PACKET_ID,
        "consumes_tranche_006_execution_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_006_EXECUTION_PACKET_ONLY_ACCEPT_LEAN_DEPENDENCY_AUDIT_SCOPE_"
            "NO_AUDIT_EXECUTION_OR_RELEASE_PROMOTION"
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
        "tranche_006_status": "lean_dependency_audit_scope_accepted_pending_execution",
        "tranche_006_cleared_for_global_release_readiness": False,
        "tranche_006_obligation_carry_forward": tranche_006,
        "global_release_readiness_still_blocked": True,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "required_remediation_type": REQUIRED_REMEDIATION_TYPE,
        "tranche_006_execution_packet_accepted": accepted,
        "tranche_006_lean_dependency_audit_scope_accepted": accepted,
        "tranche_006_audit_execution_authorized": accepted,
        "lean_dependency_audit_execution_authorized": accepted,
        "remediation_closure_execution_authorized": False,
        "remaining_release_blocking_obligations": remaining_obligations,
        "remaining_release_blocking_obligation_count": len(remaining_obligations),
        "selectable_unresolved_obligations": selectable_obligations,
        "selectable_unresolved_obligation_count": len(selectable_obligations),
        "selected_release_blocking_obligation": selected_obligation,
        "lean_dependency_audit_target": {
            "lean_target": audit_target.get("lean_target"),
            "lean_source": audit_target.get("lean_source"),
            "audit_command": audit_target.get("audit_command"),
            "executed_by_this_packet": audit_target.get("executed_by_this_packet"),
            "executed_by_this_review": False,
        },
        "required_evidence_surface": {
            "surface_kind": required_evidence.get("surface_kind"),
            "lean_target": required_evidence.get("lean_target"),
            "lean_source": required_evidence.get("lean_source"),
            "audit_command": required_evidence.get("audit_command"),
            "raw_output_required": required_evidence.get("raw_output_required"),
            "parsed_axioms_required": required_evidence.get("parsed_axioms_required"),
            "project_axioms_used_required": required_evidence.get(
                "project_axioms_used_required"
            ),
            "execution_status": required_evidence.get("execution_status"),
        },
        "execution_packet_result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "audit_execution_authorized_scope": {
            "selected_next_target": NEXT_TARGET,
            "allowed_execution_only": True,
            "does_not_authorize_blocker_movement": True,
            "does_not_authorize_release_promotion": True,
            "does_not_authorize_theorem_or_proof_debt_discharge": True,
            "carries_tranche_004_retained_blocker": True,
            "preserves_prior_documented_nonblocking_tranches": True,
        },
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "lean_dependency_audit_executed": False,
        "lean_dependency_evidence_captured": False,
        "tranche_006_audit_executed": False,
        "documentation_prepared": False,
        "policy_adjudication_executed": False,
        "expert_re_review_executed": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
        "tranche_006_moved_or_cleared": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "tranche_006_audit_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_TRANCHE_006_LEAN_AUDIT_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The execution packet result review accepts the pinned Lean dependency "
                    "audit scope and authorizes only tranche 006 audit evidence capture."
                ),
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_006",
                "decision": "deferred",
                "reason": (
                    "Full tranche 006 remediation execution remains too broad for the "
                    "immediate audit-evidence step."
                ),
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "Release readiness remains blocked by retained tranche 004 and incomplete "
                    "tranche 006 remediation."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 006 execution packet result review "
            "accepts the pinned Lean audit target for V01-ALPHA-DEP-REM-006 / "
            "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0 and authorizes "
            "only the bounded tranche 006 Lean audit execution. It carries tranche 004 as "
            "retained/release-blocking and preserves tranches 001, 002, 003, and 005 as "
            "documented_dependency_nonblocking. It does not run the audit during review, execute "
            "remediation, capture evidence, prepare documentation, execute policy adjudication "
            "or expert re-review, register blocker movement, assemble the release packet, mark "
            "v0.1-alpha readiness, discharge theorem/proof debt, discharge retained assumptions, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, "
            "promote claims, or make an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 006 execution packet "
            "result review."
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
        "v01_alpha_dependency_remediation_tranche_006_execution_packet_result_review_report: "
        f"accepted={payload['accepted']} audit_target={payload['lean_dependency_audit_target']['lean_target']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
