from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_report import (
    ADJUDICATION_QUESTION,
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET as EXPECTED_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RELEASE_HOLD_TARGET,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
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
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
    TRANCHE_006_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_20260522_v0"
EXECUTION_ID = "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_v0"
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_EXECUTED_RELEASE_HOLD_"
    "DUE_TO_RETAINED_SOURCE_MAP_BLOCKER_WITH_NO_PROMOTION"
)

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_20260522_v0.json"
)

RELEASE_READINESS_DECISION = (
    "release_readiness_held_due_to_retained_tranche_004_source_map_blocker"
)
NEXT_TARGET = "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_result"
RELEASE_HOLD_PACKET_TARGET = (
    "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker"
)
POLICY_EXCEPTION_PACKET_TARGET = (
    "prepare_v01_alpha_retained_blocker_release_policy_exception_packet"
)

FORBIDDEN_EFFECTS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "readiness_marking_authorized",
    "release_readiness_proceed_authorized",
    "release_hold_packet_prepared",
    "release_hold_registered",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_status_downgraded",
    "tranche_004_retained_blocker_discharged",
    "source_map_closure_claimed",
    "qft_gr_seam_closure_claimed",
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


def _retained_tranche_004(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("documented_dependency_nonblocking_tranches", []))


def build_adjudication(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    retained_tranche_004 = _retained_tranche_004(result_review)
    documented_rows = _documented_rows(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    release_readiness_decision = {
        "question": ADJUDICATION_QUESTION,
        "decision": RELEASE_READINESS_DECISION,
        "decision_scope": "retained_tranche_004_release_readiness_impact_only",
        "decision_basis": [
            "tranche 004 remains retained_release_blocking_source_map_blocker",
            "the current blocker is full_source_map_semantic_closure_not_authorized",
            "QFT-GR source-map closure remains unauthorized",
            "tranches 001, 002, 003, 005, and 006 are documented_dependency_nonblocking",
            "the simple dependency-remediation queue is exhausted",
            "release assembly and readiness marking require a separate governed surface",
        ],
        "meaning": (
            "v0.1-alpha release readiness cannot proceed while tranche 004 remains a "
            "retained release-blocking source-map blocker."
        ),
        "does_not_undo_documented_nonblocking_tranches": True,
        "does_not_downgrade_tranche_004": True,
        "does_not_discharge_source_map_blocker": True,
        "does_not_claim_source_map_closure": True,
        "does_not_assemble_release": True,
        "does_not_mark_readiness": True,
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_execution": result_review.get("selected_next_target")
        == EXPECTED_SELECTED_TARGET,
        "adjudication_execution_authorized": result_review.get(
            "release_readiness_adjudication_execution_authorized"
        )
        is True,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == TRANCHE_004_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == TRANCHE_004_DEPENDENCY,
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
        "tranche_005_documented_nonblocking_preserved": result_review.get("tranche_005_status")
        == TRANCHE_005_STATUS
        and result_review.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": result_review.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and result_review.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and result_review.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS,
        "documented_dependency_queue_count_expected": result_review.get(
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
        "tranche_004_retained_blocker_preserved": result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "simple_dependency_remediation_queue_exhausted": result_review.get(
            "simple_dependency_remediation_queue_exhausted"
        )
        is True,
        "adjudicates_release_readiness_impact_only": release_readiness_decision[
            "decision_scope"
        ]
        == "retained_tranche_004_release_readiness_impact_only",
        "release_readiness_decision_holds_due_to_tranche_004": release_readiness_decision[
            "decision"
        ]
        == RELEASE_READINESS_DECISION,
        "release_readiness_remains_blocked": result_review.get(
            "release_readiness_blocked_by_tranche_004"
        )
        is True
        and result_review.get("release_readiness_still_blocked") is True,
        "does_not_prepare_release_hold_packet": forbidden_effect_status[
            "release_hold_packet_prepared"
        ]
        is False
        and forbidden_effect_status["release_hold_registered"] is False,
        "does_not_assemble_release_or_mark_readiness": forbidden_effect_status[
            "release_packet_assembled"
        ]
        is False
        and forbidden_effect_status["v01_alpha_marked_ready"] is False
        and forbidden_effect_status["readiness_marking_authorized"] is False,
        "does_not_authorize_proceed": forbidden_effect_status[
            "release_readiness_proceed_authorized"
        ]
        is False,
        "does_not_downgrade_tranche_004": forbidden_effect_status[
            "tranche_004_moved_to_documented_dependency_nonblocking"
        ]
        is False
        and forbidden_effect_status["tranche_004_status_downgraded"] is False
        and forbidden_effect_status["tranche_004_retained_blocker_discharged"] is False,
        "does_not_claim_source_map_or_qft_gr_seam_closure": forbidden_effect_status[
            "source_map_closure_claimed"
        ]
        is False
        and forbidden_effect_status["qft_gr_seam_closure_claimed"] is False
        and forbidden_effect_status["seam_closure_authorized"] is False,
        "does_not_discharge_theorem_or_proof_debt": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "does_not_authorize_phase2_empirical_or_master_action": all(
            forbidden_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "execution_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_ONLY_NO_"
            "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
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
        "retained_release_blocking_obligations": result_review.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": result_review.get(
            "retained_release_blocking_obligation_count"
        ),
        "simple_dependency_remediation_queue_exhausted": True,
        "release_readiness_adjudication_question": ADJUDICATION_QUESTION,
        "release_readiness_adjudication_executed": accepted,
        "release_readiness_question_answered": accepted,
        "release_readiness_decision_made": accepted,
        "release_readiness_decision": release_readiness_decision,
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_hold_reason": "retained_tranche_004_source_map_blocker",
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
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
        "source_map_closure_claimed": False,
        "qft_gr_seam_closure_claimed": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION",
        "selected_next_target_kind": (
            "retained_tranche_004_release_readiness_adjudication_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_ONLY_NO_"
            "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The held-readiness adjudication result must be reviewed before a "
                    "release-hold packet or policy-exception packet can be prepared."
                ),
            },
            {
                "target": RELEASE_HOLD_PACKET_TARGET,
                "decision": "deferred",
                "reason": (
                    "Release-hold packet preparation is deferred until the adjudication "
                    "result review accepts the held-readiness decision."
                ),
            },
            {
                "target": POLICY_EXCEPTION_PACKET_TARGET,
                "decision": "not_authorized",
                "reason": (
                    "A release-policy exception is not authorized by this adjudication and "
                    "would require a separate governed proof/policy surface."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 release-readiness adjudication decides only that "
            "v0.1-alpha release readiness remains held while tranche 004 remains a retained "
            "release-blocking source-map blocker. It does not prepare a release-hold packet, "
            "assemble release, mark readiness, downgrade tranche 004, discharge theorem/proof "
            "debt or retained assumptions, claim source-map or QFT-GR seam closure, authorize "
            "Phase 2, validate empirically, promote the master action, or make an "
            "external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_adjudication(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_adjudication(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 release-readiness adjudication."
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
    payload = write_adjudication(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_release_readiness_adjudication_report: "
        f"accepted={payload['accepted']} decision={payload['release_readiness_decision_status']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
