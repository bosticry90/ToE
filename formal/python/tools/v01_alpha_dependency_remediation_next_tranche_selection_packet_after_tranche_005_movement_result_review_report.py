from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_005_movement_report import (
    DEFAULT_CAPTURED_AT_UTC,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_PACKET_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    SELECTED_NEXT_DEPENDENCY,
    SELECTED_NEXT_DEPENDENCY_CLASS,
    SELECTED_NEXT_FINDING_ID,
    SELECTED_NEXT_TRANCHE_ID,
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
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_005_"
    "MOVEMENT_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_005_"
    "MOVEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_AFTER_TRANCHE_005_"
    "MOVEMENT_RESULT_REVIEW_ACCEPTS_TRANCHE_006_SELECTION_AND_AUTHORIZES_TRANCHE_006_"
    "EXECUTION_PACKET_PREPARATION_ONLY"
)

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_005_MOVEMENT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_005_MOVEMENT_RESULT_REVIEW_20260515_v0.json"
)

NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_tranche_006_execution_packet"
RESULT_REVIEW_CLASSIFICATION = (
    "tranche_006_selection_accepted_execution_packet_preparation_pending"
)
SELECTION_METHOD = "stable_order_first_unresolved_non_retained_obligation"
TRANCHE_006_SOURCE_STATUS = "tracked_unresolved"


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_row(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("selected_next_remediation_tranche", {}))


def _retained_tranche_004(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("retained_tranche_004_carry_forward", {}))


def _remaining_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("remaining_release_blocking_obligations", []))


def _selectable_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("selectable_unresolved_obligations", []))


def _tranche_006_obligation(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("tranche_006_obligation_carry_forward", {}))


def build_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    selected_row = _selected_row(packet)
    retained_tranche_004 = _retained_tranche_004(packet)
    remaining_obligations = _remaining_obligations(packet)
    selectable_obligations = _selectable_obligations(packet)
    tranche_006_obligation = _tranche_006_obligation(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    packet_forbidden = dict(packet.get("forbidden_effect_status", {}))
    selection_policy = dict(packet.get("selection_policy", {}))

    acceptance_criteria = {
        "consumes_expected_after_tranche_005_movement_selection_packet": packet.get(
            "packet_id"
        )
        == EXPECTED_PACKET_ID,
        "selection_packet_accepted": packet.get("accepted") is True,
        "selection_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "selection_packet_selected_this_result_review": packet.get("selected_next_target")
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
        "tranche_004_retained_release_blocker_preserved": packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and packet.get("release_readiness_blocked_by_tranche_004") is True
        and packet.get("retained_tranche_004_release_blocker_carry_forward_required")
        is True
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "remaining_ledger_contains_retained_tranche_004_and_unresolved_tranche_006": len(
            remaining_obligations
        )
        == 2
        and [row.get("dependency_finding_id") for row in remaining_obligations]
        == [TRANCHE_004_FINDING_ID, SELECTED_NEXT_FINDING_ID]
        and remaining_obligations[0].get("status_carry_forward") == TRANCHE_004_STATUS
        and remaining_obligations[1].get("status_carry_forward")
        == TRANCHE_006_SOURCE_STATUS,
        "exactly_one_selectable_unresolved_tranche": len(selectable_obligations) == 1
        and selectable_obligations[0].get("dependency_finding_id")
        == SELECTED_NEXT_FINDING_ID,
        "selected_tranche_exact": packet.get("selected_next_tranche_id")
        == SELECTED_NEXT_TRANCHE_ID
        and selected_row.get("selected_tranche_id") == SELECTED_NEXT_TRANCHE_ID,
        "selected_finding_exact": packet.get("selected_next_dependency_finding_id")
        == SELECTED_NEXT_FINDING_ID
        and selected_row.get("selected_dependency_finding_id") == SELECTED_NEXT_FINDING_ID,
        "selected_dependency_exact": packet.get("selected_next_dependency")
        == SELECTED_NEXT_DEPENDENCY
        and selected_row.get("selected_dependency") == SELECTED_NEXT_DEPENDENCY,
        "selected_dependency_class_exact": packet.get("selected_next_dependency_class")
        == SELECTED_NEXT_DEPENDENCY_CLASS
        and selected_row.get("selected_dependency_class") == SELECTED_NEXT_DEPENDENCY_CLASS,
        "selection_method_stable_first_remaining": selected_row.get("selection_method")
        == SELECTION_METHOD
        and selection_policy.get("method") == SELECTION_METHOD
        and selection_policy.get("eligible_finding_ids") == [SELECTED_NEXT_FINDING_ID]
        and selection_policy.get("selected_finding_id") == SELECTED_NEXT_FINDING_ID,
        "tranche_006_carry_forward_matches_selection": tranche_006_obligation.get(
            "dependency_finding_id"
        )
        == SELECTED_NEXT_FINDING_ID
        and tranche_006_obligation.get("dependency") == SELECTED_NEXT_DEPENDENCY
        and tranche_006_obligation.get("dependency_class")
        == SELECTED_NEXT_DEPENDENCY_CLASS,
        "selection_count_exactly_one": packet.get("selection_count") == 1,
        "packet_prepared_selection_only": selected_row.get("execution_prepared") is False
        and selected_row.get("execution_authorized") is False
        and selected_row.get("remediation_executed") is False
        and selected_row.get("requires_result_review_before_execution_packet") is True
        and packet.get("selected_tranche_execution_packet_prepared") is False
        and packet.get("tranche_006_execution_packet_prepared") is False,
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
        "packet_forbidden_effects_all_false": all(
            packet_forbidden.get(effect) is False for effect in FORBIDDEN_EFFECTS
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "prepare_v01_alpha_dependency_remediation_tranche_006_execution_packet",
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
        else (
            "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_AFTER_TRANCHE_005_"
            "MOVEMENT_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_next_tranche_selection_packet": EXPECTED_PACKET_ID,
        "consumes_next_tranche_selection_packet_pointer": _ptr(packet_path),
        "consumed_next_tranche_selection_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_005_MOVEMENT_ONLY_"
            "ACCEPT_TRANCHE_006_SELECTION_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_tranche_004_release_blocker_carry_forward_required": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_still_blocked": True,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_005_dependency_policy_remediation_satisfied": True,
        "tranche_006_status": TRANCHE_006_SOURCE_STATUS,
        "tranche_006_obligation_carry_forward": tranche_006_obligation,
        "remaining_release_blocking_obligations": remaining_obligations,
        "remaining_release_blocking_obligation_count": len(remaining_obligations),
        "selectable_unresolved_obligations": selectable_obligations,
        "selectable_unresolved_obligation_count": len(selectable_obligations),
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
        "selection_result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "selection_count": 1 if accepted else 0,
        "selected_next_tranche_id": SELECTED_NEXT_TRANCHE_ID,
        "selected_next_dependency_finding_id": SELECTED_NEXT_FINDING_ID,
        "selected_next_dependency": SELECTED_NEXT_DEPENDENCY,
        "selected_next_dependency_class": SELECTED_NEXT_DEPENDENCY_CLASS,
        "selection_method": SELECTION_METHOD,
        "tranche_006_selection_accepted": accepted,
        "tranche_006_execution_packet_preparation_authorized": accepted,
        "tranche_006_execution_packet_prepared": False,
        "tranche_006_audit_executed": False,
        "tranche_006_moved_or_cleared": False,
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
            "TRANCHE_005_MOVEMENT_RESULT_REVIEW"
        ),
        "selected_next_target_kind": "tranche_006_execution_packet_preparation_only",
        "next_action_scope": (
            "PREPARE_TRANCHE_006_EXECUTION_PACKET_ONLY_NO_REMEDIATION_EXECUTION_OR_"
            "RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The result review accepts tranche 006 selection and authorizes only "
                    "preparation of its execution packet."
                ),
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_006_audit",
                "decision": "deferred",
                "reason": (
                    "Tranche 006 audit execution requires an execution packet and result "
                    "review first."
                ),
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "Release readiness remains blocked by retained tranche 004; this review "
                    "continues queue processing only."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation next-tranche selection packet result "
            "review after tranche 005 movement accepts only the tranche 006 selection for "
            "V01-ALPHA-DEP-REM-006 / "
            "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0 and "
            "authorizes only tranche 006 execution-packet preparation. It carries tranche "
            "004 as retained/release-blocking and does not execute remediation, prepare the "
            "tranche 006 execution packet during review, move or discharge tranche 004, "
            "register blocker movement, assemble release, mark v0.1-alpha readiness, "
            "discharge theorem/proof debt, discharge retained assumptions, authorize "
            "Phase 2, close seams, validate empirically, promote the master action, "
            "or make an external-truth claim."
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
            "result review after tranche 005 movement."
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
        "v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_005_movement_result_review_report: "
        f"accepted={payload['accepted']} selected_next_tranche={payload['selected_next_tranche_id']} "
        f"selected_next_dependency={payload['selected_next_dependency']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
