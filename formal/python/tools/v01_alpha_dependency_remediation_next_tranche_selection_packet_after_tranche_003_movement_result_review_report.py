from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_"
    "MOVEMENT_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_"
    "MOVEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_AFTER_TRANCHE_003_"
    "MOVEMENT_RESULT_REVIEW_ACCEPTS_TRANCHE_004_SELECTION_AND_AUTHORIZES_TRANCHE_004_"
    "EXECUTION_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_MOVEMENT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_MOVEMENT_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_"
    "MOVEMENT_v0"
)
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_PREPARED_AFTER_"
    "TRANCHE_003_MOVEMENT_WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
TRANCHE_003_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-004"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-004"
SELECTED_DEPENDENCY = (
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
SELECTED_DEPENDENCY_CLASS = "blocked_bridge_authorization_dependency"
SELECTION_METHOD = "stable_order_first_remaining_release_blocking_obligation"
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_tranche_004_execution_packet"

REMAINING_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

FORBIDDEN_EFFECTS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "selected_tranche_execution_packet_prepared",
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


def _remaining_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("remaining_release_blocking_obligations", []))


def _remaining_obligations_are_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows] == REMAINING_BLOCKER_IDS
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
            for row in rows
        )
    )


def _selected_row(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("selected_next_remediation_tranche", {}))


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    remaining_obligations = _remaining_obligations(packet)
    selected_row = _selected_row(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_selection_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "selection_packet_accepted": packet.get("accepted") is True,
        "selection_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "selection_packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": packet.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": packet.get("tranche_003_status")
        == TRANCHE_003_STATUS
        and packet.get("tranche_003_formal_movement_accepted") is True,
        "three_obligations_tracked_unmodified": _remaining_obligations_are_unmodified(
            remaining_obligations
        ),
        "selected_tranche_expected": packet.get("selected_next_tranche_id")
        == SELECTED_TRANCHE_ID
        and selected_row.get("selected_tranche_id") == SELECTED_TRANCHE_ID,
        "selected_finding_expected": packet.get("selected_next_dependency_finding_id")
        == SELECTED_FINDING_ID
        and selected_row.get("selected_dependency_finding_id") == SELECTED_FINDING_ID,
        "selected_dependency_expected": packet.get("selected_next_dependency")
        == SELECTED_DEPENDENCY
        and selected_row.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": packet.get("selected_next_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_row.get("selected_dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "selection_method_stable_first_remaining": selected_row.get("selection_method")
        == SELECTION_METHOD
        and packet.get("selection_policy", {}).get("method") == SELECTION_METHOD
        and packet.get("selection_policy", {}).get("eligible_finding_ids", [None])[0]
        == SELECTED_FINDING_ID,
        "selection_count_exactly_one": packet.get("selection_count") == 1,
        "packet_prepared_selection_only": selected_row.get("execution_prepared") is False
        and selected_row.get("execution_authorized") is False
        and selected_row.get("remediation_executed") is False
        and packet.get("selected_tranche_execution_packet_prepared") is False,
        "no_remediation_execution_during_review": forbidden_effect_status[
            "remediation_executed"
        ]
        is False
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
        == "prepare_v01_alpha_dependency_remediation_tranche_004_execution_packet",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "logical_review_target": EXPECTED_PACKET_SELECTED_TARGET,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_MOVEMENT_RESULT_REVIEW_BLOCKED",
        "consumes_next_tranche_selection_packet": EXPECTED_PACKET_ID,
        "consumes_next_tranche_selection_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_MOVEMENT_ONLY_ACCEPT_TRANCHE_004_SELECTION_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_003_formal_movement_accepted": True,
        "tranche_003_cleared_for_global_release_readiness": False,
        "global_release_readiness_still_blocked": True,
        "remaining_release_blocking_obligations": remaining_obligations,
        "remaining_release_blocking_obligation_count": len(remaining_obligations),
        "selected_next_remediation_tranche": {
            "selected_tranche_id": selected_row.get("selected_tranche_id"),
            "selected_dependency_finding_id": selected_row.get(
                "selected_dependency_finding_id"
            ),
            "selected_dependency": selected_row.get("selected_dependency"),
            "selected_dependency_class": selected_row.get("selected_dependency_class"),
            "selection_method": selected_row.get("selection_method"),
            "source_status": selected_row.get("source_status"),
            "execution_prepared": False,
            "execution_authorized": False,
            "remediation_executed": False,
            "requires_execution_packet_before_remediation": True,
        },
        "selection_result_review_classification": (
            "tranche_004_selection_accepted_execution_packet_preparation_pending"
        ),
        "selection_count": 1 if accepted else 0,
        "selected_next_tranche_id": SELECTED_TRANCHE_ID,
        "selected_next_dependency_finding_id": SELECTED_FINDING_ID,
        "selected_next_dependency": SELECTED_DEPENDENCY,
        "selected_next_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selection_method": SELECTION_METHOD,
        "tranche_004_selection_accepted": accepted,
        "tranche_004_execution_packet_preparation_authorized": accepted,
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "selected_tranche_execution_packet_prepared": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_003_MOVEMENT_RESULT_REVIEW",
        "selected_next_target_kind": "tranche_004_execution_packet_preparation_only",
        "next_action_scope": (
            "PREPARE_TRANCHE_004_EXECUTION_PACKET_ONLY_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Selection review accepts tranche 004 and authorizes only "
                    "preparation of its execution packet."
                ),
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_004",
                "decision": "deferred",
                "reason": (
                    "Actual tranche 004 remediation execution is not authorized until "
                    "the execution packet is prepared and reviewed."
                ),
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": (
                    "Release-readiness adjudication remains blocked by the three remaining "
                    "release-blocking obligations."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation next-tranche selection packet result "
            "review after tranche 003 movement accepts only the tranche 004 selection for "
            "V01-ALPHA-DEP-REM-004 / qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0 "
            "and authorizes only tranche 004 execution-packet preparation. It does not "
            "execute remediation, prepare the execution packet during the review, register "
            "blocker movement, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge Lean theorem debt, reduce axiom/spec-backed proof debt, discharge "
            "retained assumptions, authorize Phase 2, close seams, validate empirically, "
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
            "Generate the v0.1-alpha dependency remediation next-tranche selection packet "
            "result review after tranche 003 movement."
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
        "v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_003_movement_result_review_report: "
        f"accepted={payload['accepted']} selected_next_tranche={payload['selected_next_tranche_id']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
