from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_"
    "20260515_v0"
)
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_AUDIT_TARGET_AND_AUTHORIZES_TRANCHE_002_AUDIT_EXECUTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_v0"
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_PREPARED_FOR_"
    "STATIONARY_IMPLIES_OPERATOR_ZERO_WITH_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_002_execution_packet_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-002"
SELECTED_DEPENDENCY = "stationary_implies_operator_zero"
SELECTED_DEPENDENCY_CLASS = "lean_theorem_dependency"
LEAN_TARGET = "ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
LEAN_SOURCE = "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean"
LEAN_AUDIT_COMMAND = (
    "#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
)
NEXT_TARGET = "execute_v01_alpha_dependency_remediation_tranche_002_audit"

FORBIDDEN_EFFECTS = [
    "remediation_executed",
    "lean_dependency_audit_executed",
    "lean_dependency_evidence_captured",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_movement_registered",
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


def _release_blockers_are_carried_forward(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


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
    release_blockers = _release_blockers(packet)
    selected_obligation = _selected_obligation(release_blockers)
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
        "tranche_002_only_selected_target": packet.get("selection_count") == 1
        and packet.get("selected_tranche_id") == SELECTED_TRANCHE_ID
        and packet.get("selected_remediation_finding_id") == SELECTED_FINDING_ID,
        "selected_dependency_expected": packet.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": packet.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_exact": audit_target.get("lean_target") == LEAN_TARGET
        and audit_target.get("lean_source") == LEAN_SOURCE
        and audit_target.get("audit_command") == LEAN_AUDIT_COMMAND,
        "required_evidence_surface_exact": required_evidence.get("lean_target") == LEAN_TARGET
        and required_evidence.get("audit_command") == LEAN_AUDIT_COMMAND
        and required_evidence.get("execution_status") == "prepared_not_executed_v0",
        "no_audit_execution_in_packet_or_review": packet.get("lean_dependency_audit_executed")
        is False
        and packet.get("lean_dependency_evidence_captured") is False
        and audit_target.get("executed_by_this_packet") is False
        and forbidden_effect_status["lean_dependency_audit_executed"] is False
        and forbidden_effect_status["lean_dependency_evidence_captured"] is False,
        "no_remediation_execution": packet.get("remediation_executed") is False
        and forbidden_effect_status["remediation_executed"] is False,
        "all_five_release_blockers_carried_forward": _release_blockers_are_carried_forward(
            release_blockers
        ),
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
        == "execute_v01_alpha_dependency_remediation_tranche_002_audit",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_tranche_002_execution_packet": EXPECTED_PACKET_ID,
        "consumes_tranche_002_execution_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_002_EXECUTION_PACKET_ONLY_ACCEPT_AUDIT_TARGET_NO_AUDIT_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_001_formal_movement_accepted": True,
        "tranche_001_cleared_for_global_release_readiness": False,
        "global_release_readiness_still_blocked": True,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "tranche_002_execution_packet_accepted": accepted,
        "tranche_002_audit_target_accepted": accepted,
        "tranche_002_audit_execution_authorized": accepted,
        "lean_dependency_audit_execution_authorized": accepted,
        "remediation_closure_execution_authorized": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
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
        "execution_packet_result_review_classification": (
            "audit_target_accepted_audit_execution_authorized_only"
        ),
        "remediation_executed": False,
        "lean_dependency_audit_executed": False,
        "lean_dependency_evidence_captured": False,
        "documentation_prepared": False,
        "expert_re_review_executed": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "tranche_002_audit_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_TRANCHE_002_LEAN_AUDIT_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The execution packet result review accepts the pinned Lean audit target and authorizes only audit evidence capture.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "Full tranche 002 remediation execution remains too broad for the immediate audit-evidence step.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tracked release-blocking obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 002 execution packet result review "
            "accepts the pinned audit target for V01-ALPHA-DEP-REM-002 / "
            "stationary_implies_operator_zero and authorizes only the bounded tranche 002 Lean "
            "audit execution. It does not run the audit during review, execute remediation, capture "
            "evidence, prepare documentation, execute expert re-review, register blocker movement, "
            "assemble the release packet, mark v0.1-alpha readiness, discharge theorem/proof debt, "
            "discharge retained assumptions, authorize Phase 2, close seams, validate empirically, "
            "promote the master action, promote claims, or make an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 002 execution packet "
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
        "v01_alpha_dependency_remediation_tranche_002_execution_packet_result_review_report: "
        f"accepted={payload['accepted']} audit_target={payload['lean_dependency_audit_target']['lean_target']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
