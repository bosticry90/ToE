from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_summary_after_tranche_006_movement_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET as EXPECTED_SUMMARY_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_SUMMARY_OUTCOME,
    PACKET_ID as EXPECTED_SUMMARY_PACKET_ID,
    SCHEMA_ID as EXPECTED_SUMMARY_SCHEMA_ID,
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
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
    TRANCHE_006_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_20260522_v0"
)
PACKET_ID = "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_PREPARED_"
    "WITH_NO_RELEASE_ASSEMBLY_OR_READINESS_PROMOTION"
)

DEFAULT_SUMMARY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_20260522_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_20260522_v0.json"
)

SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-004"
NEXT_TARGET = "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result"
EXECUTION_TARGET = "execute_v01_alpha_retained_tranche_004_release_readiness_adjudication"
RELEASE_HOLD_TARGET = "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_blocker"
PACKET_CLASSIFICATION = "retained_tranche_004_release_readiness_adjudication_question_prepared"
ADJUDICATION_QUESTION = (
    "Can v0.1-alpha release-readiness proceed with tranche 004 retained as a documented "
    "release blocker, or does tranche 004 force a release hold?"
)

FORBIDDEN_EFFECTS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_hold_packet_prepared",
    "release_hold_registered",
    "release_readiness_adjudication_executed",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_status_downgraded",
    "tranche_004_retained_blocker_discharged",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "lane_reopen_authorized",
    "computational_physics_execution_surface_opened",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def build_packet(
    *,
    summary_path: Path = DEFAULT_SUMMARY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    summary = _read_json(summary_path)
    retained_tranche_004 = dict(summary.get("retained_tranche_004_carry_forward", {}))
    retained_release_blockers = list(summary.get("retained_release_blocking_obligations", []))
    documented_tranches = list(summary.get("documented_dependency_nonblocking_tranches", []))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_summary": summary.get("packet_id") == EXPECTED_SUMMARY_PACKET_ID,
        "summary_schema_expected": summary.get("schema_id") == EXPECTED_SUMMARY_SCHEMA_ID,
        "summary_accepted": summary.get("accepted") is True,
        "summary_outcome_expected": summary.get("outcome_id") == EXPECTED_SUMMARY_OUTCOME,
        "summary_selected_this_packet": summary.get("selected_next_target")
        == EXPECTED_SUMMARY_SELECTED_TARGET,
        "tranches_001_002_003_005_006_documented_nonblocking": summary.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and summary.get("tranche_002_status") == TRANCHE_002_STATUS
        and summary.get("tranche_003_status") == TRANCHE_003_STATUS
        and summary.get("tranche_005_status") == TRANCHE_005_STATUS
        and summary.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and summary.get("tranche_006_status") == TRANCHE_006_STATUS
        and summary.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and summary.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_004_retained_release_blocker_preserved": summary.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "simple_dependency_remediation_queue_exhausted": summary.get(
            "simple_dependency_remediation_queue_exhausted"
        )
        is True
        and summary.get("unresolved_simple_dependency_tranche_count") == 0,
        "release_readiness_still_blocked": summary.get("release_readiness_still_blocked")
        is True
        and summary.get("release_readiness_blocked_by_tranche_004") is True,
        "prepares_retained_blocker_adjudication_only": ADJUDICATION_QUESTION
        == (
            "Can v0.1-alpha release-readiness proceed with tranche 004 retained as a "
            "documented release blocker, or does tranche 004 force a release hold?"
        ),
        "does_not_assemble_release": summary.get("release_packet_assembled") is False
        and forbidden_effect_status["release_packet_assembled"] is False,
        "does_not_mark_release_readiness": summary.get("v01_alpha_marked_ready") is False
        and forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "does_not_downgrade_tranche_004": forbidden_effect_status[
            "tranche_004_moved_to_documented_dependency_nonblocking"
        ]
        is False
        and forbidden_effect_status["tranche_004_status_downgraded"] is False
        and forbidden_effect_status["tranche_004_retained_blocker_discharged"] is False,
        "does_not_discharge_theorem_or_proof_debt": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "does_not_authorize_phase2_seam_empirical_or_master_action": all(
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
        == "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result",
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_BLOCKED",
        "consumes_dependency_remediation_summary_after_tranche_006_movement": EXPECTED_SUMMARY_PACKET_ID,
        "consumes_dependency_remediation_summary_after_tranche_006_movement_pointer": _ptr(
            summary_path
        ),
        "consumed_dependency_remediation_summary_schema_id": summary.get("schema_id"),
        "packet_scope": (
            "PREPARE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_ONLY_NO_"
            "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "documented_dependency_nonblocking_tranches": documented_tranches,
        "documented_dependency_nonblocking_tranche_count": len(documented_tranches),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_tranche_id": TRANCHE_006_TRANCHE_ID,
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_dependency_finding_id": TRANCHE_006_FINDING_ID,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": retained_release_blockers,
        "retained_release_blocking_obligation_count": len(retained_release_blockers),
        "simple_dependency_remediation_queue_exhausted": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_still_blocked": True,
        "release_readiness_adjudication_question": ADJUDICATION_QUESTION,
        "release_readiness_adjudication_packet_prepared": True,
        "release_readiness_adjudication_executed": False,
        "release_readiness_question_answered": False,
        "release_hold_packet_prepared": False,
        "release_hold_registered": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_downgraded": False,
        "tranche_004_retained_blocker_discharged": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET",
        "selected_next_target_kind": (
            "retained_tranche_004_release_readiness_adjudication_packet_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_ONLY_"
            "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The packet is prepared, so the next bounded step is to review that the "
                    "retained-blocker release-readiness question was framed without answering it."
                ),
            },
            {
                "target": EXECUTION_TARGET,
                "decision": "deferred",
                "reason": (
                    "Execution is not authorized until packet-result review confirms the "
                    "question-only boundary and retained-blocker posture."
                ),
            },
            {
                "target": RELEASE_HOLD_TARGET,
                "decision": "deferred",
                "reason": (
                    "A release-hold packet remains available if the retained-blocker "
                    "adjudication later fails closed, but this packet does not choose that path."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 release-readiness adjudication packet prepares only the "
            "question of whether v0.1-alpha can proceed while tranche 004 remains a documented "
            "release blocker. It does not answer that question, assemble release, mark "
            "readiness, downgrade tranche 004, discharge theorem/proof debt or retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the "
            "master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    summary_path: Path = DEFAULT_SUMMARY_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(summary_path=summary_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 release-readiness adjudication packet."
        )
    )
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    summary_path = ns.summary if ns.summary.is_absolute() else (REPO_ROOT / ns.summary)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_packet(
        summary_path=summary_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
