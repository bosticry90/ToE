from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_report import (
    ADJUDICATION_QUESTION,
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET as EXPECTED_PACKET_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    RELEASE_HOLD_TARGET,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SELECTED_TRANCHE_ID,
    EXECUTION_TARGET as NEXT_TARGET,
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
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_RETAINED_BLOCKER_ADJUDICATION_QUESTION_AND_AUTHORIZES_ADJUDICATION_EXECUTION_ONLY"
)

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_20260522_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0.json"
)

FORBIDDEN_EFFECTS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_hold_packet_prepared",
    "release_hold_registered",
    "release_readiness_adjudication_executed",
    "release_readiness_question_answered",
    "release_readiness_decision_made",
    "release_readiness_proceed_authorized",
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


def _retained_tranche_004(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("documented_dependency_nonblocking_tranches", []))


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    retained_tranche_004 = _retained_tranche_004(packet)
    documented_rows = _documented_rows(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_accepted": packet.get("accepted") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_selected_this_review": packet.get("selected_next_target")
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
        "tranche_006_documented_nonblocking_preserved": packet.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and packet.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and packet.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS,
        "documented_dependency_queue_count_expected": packet.get(
            "documented_dependency_nonblocking_tranche_count"
        )
        == 5
        and [row.get("finding_id") for row in documented_rows]
        == [
            "V01-ALPHA-DEP-REM-001",
            "V01-ALPHA-DEP-REM-002",
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ],
        "tranche_004_retained_release_blocker_preserved": packet.get(
            "tranche_004_status"
        )
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "simple_dependency_remediation_queue_exhausted": packet.get(
            "simple_dependency_remediation_queue_exhausted"
        )
        is True,
        "adjudication_question_prepared_only": packet.get(
            "release_readiness_adjudication_question"
        )
        == ADJUDICATION_QUESTION
        and packet.get("release_readiness_adjudication_packet_prepared") is True
        and packet.get("release_readiness_adjudication_executed") is False
        and packet.get("release_readiness_question_answered") is False,
        "release_readiness_remains_blocked": packet.get(
            "release_readiness_blocked_by_tranche_004"
        )
        is True
        and packet.get("release_readiness_still_blocked") is True,
        "does_not_prepare_hold_packet": packet.get("release_hold_packet_prepared")
        is False
        and packet.get("release_hold_registered") is False
        and forbidden_effect_status["release_hold_packet_prepared"] is False,
        "does_not_assemble_release_or_mark_readiness": packet.get(
            "release_packet_assembled"
        )
        is False
        and packet.get("v01_alpha_marked_ready") is False
        and forbidden_effect_status["release_packet_assembled"] is False
        and forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "does_not_downgrade_tranche_004": packet.get(
            "tranche_004_moved_to_documented_dependency_nonblocking"
        )
        is False
        and packet.get("tranche_004_status_downgraded") is False
        and packet.get("tranche_004_retained_blocker_discharged") is False,
        "does_not_discharge_theorem_or_proof_debt": packet.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and packet.get("proof_debt_reduced") is False
        and packet.get("axiom_spec_backed_debt_reduced") is False,
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
        "authorizes_adjudication_execution_only": NEXT_TARGET
        == "execute_v01_alpha_retained_tranche_004_release_readiness_adjudication",
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_packet": EXPECTED_PACKET_ID,
        "consumes_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_ONLY_"
            "AUTHORIZE_ADJUDICATION_EXECUTION_NO_RELEASE_DECISION"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
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
        "documented_dependency_nonblocking_tranches": documented_rows,
        "documented_dependency_nonblocking_tranche_count": len(documented_rows),
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": packet.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": packet.get(
            "retained_release_blocking_obligation_count"
        ),
        "simple_dependency_remediation_queue_exhausted": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_still_blocked": True,
        "retained_blocker_adjudication_question_accepted": accepted,
        "release_readiness_adjudication_question": ADJUDICATION_QUESTION,
        "release_readiness_adjudication_execution_authorized": accepted,
        "release_readiness_adjudication_execution_scope": (
            "DECIDE_ONLY_WHETHER_V01_ALPHA_CAN_PROCEED_WITH_TRANCHE_004_RETAINED_OR_"
            "MUST_HOLD_RELEASE"
        ),
        "release_readiness_adjudication_executed": False,
        "release_readiness_question_answered": False,
        "release_readiness_decision_made": False,
        "release_readiness_proceed_authorized": False,
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": (
            "retained_tranche_004_release_readiness_adjudication_execution_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_ONLY_NO_"
            "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The question-only packet is accepted, so the next bounded step may "
                    "execute the retained-tranche-004 release-readiness adjudication."
                ),
            },
            {
                "target": RELEASE_HOLD_TARGET,
                "decision": "deferred",
                "reason": (
                    "A release-hold packet is deferred until adjudication answers that "
                    "tranche 004 forces a hold."
                ),
            },
            {
                "target": "assemble_v01_alpha_release_packet",
                "decision": "not_authorized",
                "reason": (
                    "Release assembly remains blocked until retained-tranche-004 "
                    "release-readiness adjudication is executed and reviewed."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 release-readiness adjudication packet result review "
            "accepts only that the retained-blocker release-readiness question was prepared "
            "and authorizes only the next bounded adjudication execution step. It does not "
            "answer the release-readiness question, prepare a release-hold packet, assemble "
            "release, mark readiness, downgrade tranche 004, discharge theorem/proof debt or "
            "retained assumptions, authorize Phase 2, close seams, validate empirically, "
            "promote the master action, or make an external-truth claim."
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
            "Generate the v0.1-alpha retained tranche 004 release-readiness adjudication "
            "packet result review."
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
        "v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
