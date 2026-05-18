from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_"
    "RETAINED_BLOCKER_DECLARATION_20260515_v0"
)
PACKET_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_"
    "RETAINED_BLOCKER_DECLARATION_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_AFTER_TRANCHE_004_"
    "RETAINED_BLOCKER_PREPARED_WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_"
    "ACCEPTS_RETAINED_RELEASE_BLOCKER_AND_SELECTS_REMEDIATION_CONTINUATION_OR_RELEASE_HOLD"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_"
    "retained_blocker_declaration"
)
EXPECTED_ROUTING_DECISION = (
    "continue_to_tranche_005_selection_while_carrying_tranche_004_as_retained_release_blocker"
)

TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
TRANCHE_003_STATUS = "documented_dependency_nonblocking"
TRANCHE_004_STATUS = "retained_release_blocking_source_map_blocker"
TRANCHE_004_FINDING_ID = "V01-ALPHA-DEP-REM-004"
TRANCHE_004_DEPENDENCY = (
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
TRANCHE_004_DEPENDENCY_CLASS = "blocked_bridge_authorization_dependency"

SELECTED_NEXT_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-005"
SELECTED_NEXT_FINDING_ID = "V01-ALPHA-DEP-REM-005"
SELECTED_NEXT_DEPENDENCY = "supplied_interface_alignment_semantics_construct_bridge_package_v0"
SELECTED_NEXT_DEPENDENCY_CLASS = "lean_bridge_dependency"
NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_"
    "retained_blocker_declaration_result"
)

RETAINED_BLOCKER_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
TRANCHE_004_CURRENT_BLOCKER = "full_source_map_semantic_closure_not_authorized"
CONSTRUCTION_ATTEMPT_CLASSIFICATION = "construction_attempt_failed_retained_blocker"
DECLARATION_CLASSIFICATION = (
    "retained_source_map_authorization_release_blocker_declared_after_fail_closed_attempt"
)

UNRESOLVED_NON_TRANCHE_004_IDS = [
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

FORBIDDEN_EFFECTS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "selected_tranche_execution_packet_prepared",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
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


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _other_unresolved_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_NEXT_FINDING_ID:
            return dict(row)
    return {}


def _tranche_004_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == TRANCHE_004_FINDING_ID:
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


def _unresolved_non_tranche_004_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 2
        and [row.get("dependency_finding_id") for row in rows] == UNRESOLVED_NON_TRANCHE_004_IDS
        and all(row.get("modified_by_tranche_004") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_004"
            for row in rows
        )
    )


def _selection_row(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "selected_tranche_id": SELECTED_NEXT_TRANCHE_ID,
        "selected_dependency_finding_id": row.get("dependency_finding_id"),
        "selected_dependency": row.get("dependency"),
        "selected_dependency_class": row.get("dependency_class"),
        "source_status": row.get("status_carry_forward"),
        "selection_method": "stable_order_first_unresolved_non_tranche_004_obligation",
        "selection_reason": (
            "Tranche 004 is carried as retained/release-blocking. This is the first "
            "unresolved non-tranche-004 obligation in the current remediation ledger."
        ),
        "execution_prepared": False,
        "execution_authorized": False,
        "remediation_executed": False,
        "requires_result_review_before_execution_packet": True,
    }


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    release_blockers = _release_blockers(result_review)
    unresolved_non_tranche_004 = _other_unresolved_obligations(result_review)
    selected_obligation = _selected_obligation(unresolved_non_tranche_004)
    retained_tranche_004 = _tranche_004_obligation(release_blockers)
    selected_row = _selection_row(selected_obligation)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    retained_tranche_004_carry_forward = {
        "tranche_id": "V01-ALPHA-DEP-REM-TRANCHE-004",
        "dependency_finding_id": TRANCHE_004_FINDING_ID,
        "dependency": TRANCHE_004_DEPENDENCY,
        "dependency_class": TRANCHE_004_DEPENDENCY_CLASS,
        "status": TRANCHE_004_STATUS,
        "current_blocker": TRANCHE_004_CURRENT_BLOCKER,
        "retained_blocker_reason": RETAINED_BLOCKER_REASON,
        "construction_attempt_classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "declaration_classification": DECLARATION_CLASSIFICATION,
        "release_readiness_blocked_by_tranche_004": True,
        "moved_to_documented_dependency_nonblocking": False,
        "source_ledger_row": retained_tranche_004,
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "result_review_routing_decision_expected": result_review.get("routing_decision_token")
        == EXPECTED_ROUTING_DECISION,
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
        "tranche_004_retained_release_blocker_preserved": result_review.get(
            "retained_blocker"
        )
        is True
        and result_review.get("remains_release_blocking") is True
        and result_review.get("release_readiness_blocked_by_tranche_004") is True
        and result_review.get("tranche_004_moved_to_documented_dependency_nonblocking")
        is False,
        "tranche_004_identity_preserved": result_review.get("selected_remediation_finding_id")
        == TRANCHE_004_FINDING_ID
        and result_review.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "tranche_004_source_map_blocker_preserved": result_review.get("current_blocker")
        == TRANCHE_004_CURRENT_BLOCKER
        and result_review.get("blocker_reason") == RETAINED_BLOCKER_REASON,
        "tranche_004_attempt_and_declaration_preserved": result_review.get(
            "construction_attempt_classification"
        )
        == CONSTRUCTION_ATTEMPT_CLASSIFICATION
        and result_review.get("declaration_classification") == DECLARATION_CLASSIFICATION,
        "all_release_blockers_carried": _release_blockers_tracked(release_blockers),
        "two_unresolved_non_tranche_004_obligations_carried": _unresolved_non_tranche_004_tracked(
            unresolved_non_tranche_004
        ),
        "selected_row_present": selected_obligation.get("dependency_finding_id")
        == SELECTED_NEXT_FINDING_ID,
        "selected_row_expected_dependency": selected_row.get("selected_dependency")
        == SELECTED_NEXT_DEPENDENCY
        and selected_row.get("selected_dependency_class") == SELECTED_NEXT_DEPENDENCY_CLASS,
        "selects_exactly_one_next_tranche": selected_row["selected_tranche_id"]
        == SELECTED_NEXT_TRANCHE_ID
        and selected_row["selected_dependency_finding_id"] == SELECTED_NEXT_FINDING_ID,
        "stable_first_remaining_blocker_rule_used": selected_row["selection_method"]
        == "stable_order_first_unresolved_non_tranche_004_obligation"
        and unresolved_non_tranche_004[0].get("dependency_finding_id")
        == SELECTED_NEXT_FINDING_ID,
        "selection_preparation_only": selected_row["execution_prepared"] is False
        and selected_row["execution_authorized"] is False
        and selected_row["remediation_executed"] is False,
        "release_readiness_still_blocked": result_review.get(
            "release_readiness_blocked_by_tranche_004"
        )
        is True
        and forbidden_effect_status["release_readiness_adjudication_prepared"] is False,
        "no_tranche_004_movement": forbidden_effect_status[
            "tranche_004_moved_to_documented_dependency_nonblocking"
        ]
        is False
        and forbidden_effect_status["tranche_004_retained_blocker_discharged"] is False,
        "no_remediation_execution": forbidden_effect_status["remediation_executed"] is False
        and forbidden_effect_status["remediation_execution_authorized"] is False,
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
        == (
            "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_"
            "retained_blocker_declaration_result"
        ),
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
        else (
            "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_AFTER_TRANCHE_004_"
            "RETAINED_BLOCKER_BLOCKED"
        ),
        "consumes_retained_blocker_declaration_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_retained_blocker_declaration_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_retained_blocker_declaration_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "packet_scope": (
            "PREPARE_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
            "DECLARATION_ONLY_NO_REMEDIATION_EXECUTION_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004_carry_forward,
        "retained_tranche_004_release_blocker_carry_forward_required": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_still_blocked": True,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "unresolved_non_tranche_004_obligations": unresolved_non_tranche_004,
        "unresolved_non_tranche_004_obligation_count": len(unresolved_non_tranche_004),
        "selected_next_remediation_tranche": selected_row,
        "selected_next_tranche_id": selected_row.get("selected_tranche_id"),
        "selected_next_dependency_finding_id": selected_row.get(
            "selected_dependency_finding_id"
        ),
        "selected_next_dependency": selected_row.get("selected_dependency"),
        "selected_next_dependency_class": selected_row.get("selected_dependency_class"),
        "selection_count": 1 if accepted else 0,
        "selection_policy": {
            "method": "stable_order_first_unresolved_non_tranche_004_obligation",
            "eligible_finding_ids": [
                row.get("dependency_finding_id") for row in unresolved_non_tranche_004
            ],
            "selected_finding_id": selected_row.get("selected_dependency_finding_id"),
            "retained_tranche_004_excluded_from_next_selection": True,
            "retained_tranche_004_carried_forward": True,
            "does_not_execute_selection": True,
            "requires_result_review_before_execution_packet": True,
        },
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "selected_tranche_execution_packet_prepared": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
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
        else (
            "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_AFTER_"
            "TRANCHE_004_RETAINED_BLOCKER"
        ),
        "selected_next_target_kind": (
            "next_tranche_selection_after_tranche_004_retained_blocker_result_review_only"
        ),
        "next_action_scope": (
            "REVIEW_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
            "DECLARATION_ONLY_NO_REMEDIATION_EXECUTION_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The next-tranche selection packet must be reviewed before tranche 005 "
                    "execution-packet preparation."
                ),
            },
            {
                "target": (
                    "prepare_v01_alpha_dependency_remediation_tranche_005_execution_packet"
                ),
                "decision": "deferred",
                "reason": "Tranche 005 execution-packet preparation requires selection result review first.",
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": "Release readiness remains blocked by tranche 004, but this packet prepares tranche selection only.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation next-tranche selection packet after "
            "tranche 004 retained-blocker declaration carries tranche 004 as retained/"
            "release-blocking and selects only tranche 005 from the current unresolved "
            "non-tranche-004 ledger. It does not execute remediation, prepare the tranche "
            "005 execution packet, move tranche 004, assemble release, mark readiness, "
            "discharge theorem/proof debt, authorize Phase 2, close seams, validate "
            "empirically, promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation next-tranche selection packet "
            "after tranche 004 retained-blocker declaration."
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
    payload = write_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_report: "
        f"accepted={payload['accepted']} selected_next_tranche={payload['selected_next_tranche_id']} "
        f"selected_next_dependency={payload['selected_next_dependency']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
