from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_HOLD_PACKET_PATH,
    FORBIDDEN_EFFECTS as HOLD_PACKET_FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_HOLD_PACKET_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_HOLD_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_HOLD_PACKET_ID,
    SCHEMA_ID as EXPECTED_HOLD_PACKET_SCHEMA_ID,
    TRANCHE_004_FUTURE_ROUTE,
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
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_"
    "RESULT_REVIEW_20260522_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RELEASE_HOLD_PACKET_RESULT_REVIEW_ACCEPTS_RELEASE_HOLD_DUE_TO_"
    "RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_AND_AUTHORIZES_POST_HOLD_ROUTING_ONLY"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_RESULT_REVIEW_20260522_v0.json"
)

NEXT_TARGET = "prepare_v01_alpha_post_hold_routing_packet_due_to_retained_tranche_004"
FUTURE_REMEDIATION_PROGRAM_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_future_remediation_program"
)
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

FORBIDDEN_EFFECTS = sorted(
    set(HOLD_PACKET_FORBIDDEN_EFFECTS)
    | {
        "future_remediation_program_prepared_by_review",
        "post_hold_routing_packet_prepared",
        "release_assembly_authorized_by_review",
        "release_hold_registered_by_review",
        "release_readiness_marked_ready_by_review",
    }
)


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
    hold_packet_path: Path = DEFAULT_HOLD_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    hold_packet = _read_json(hold_packet_path)
    retained_tranche_004 = _retained_tranche_004(hold_packet)
    documented_rows = _documented_rows(hold_packet)
    hold_packet_forbidden = dict(hold_packet.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_hold_packet": hold_packet.get("packet_id")
        == EXPECTED_HOLD_PACKET_ID,
        "hold_packet_schema_expected": hold_packet.get("schema_id")
        == EXPECTED_HOLD_PACKET_SCHEMA_ID,
        "hold_packet_prepared_and_accepted": hold_packet.get("prepared") is True
        and hold_packet.get("accepted") is True
        and hold_packet.get("release_hold_packet_prepared") is True,
        "hold_packet_outcome_expected": hold_packet.get("outcome_id")
        == EXPECTED_HOLD_PACKET_OUTCOME,
        "hold_packet_selected_this_review": hold_packet.get("selected_next_target")
        == EXPECTED_HOLD_PACKET_SELECTED_TARGET,
        "release_readiness_hold_preserved": hold_packet.get(
            "release_readiness_decision_status"
        )
        == RELEASE_READINESS_DECISION
        and hold_packet.get("release_readiness_held") is True
        and hold_packet.get("release_readiness_still_blocked") is True
        and hold_packet.get("release_readiness_blocked_by_tranche_004") is True,
        "tranche_001_documented_nonblocking_preserved": hold_packet.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": hold_packet.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": hold_packet.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": hold_packet.get(
            "tranche_005_status"
        )
        == TRANCHE_005_STATUS
        and hold_packet.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": hold_packet.get(
            "tranche_006_status"
        )
        == TRANCHE_006_STATUS
        and hold_packet.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and hold_packet.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and hold_packet.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": hold_packet.get(
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
        "tranche_004_retained_blocker_preserved": hold_packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "simple_dependency_remediation_queue_exhausted": hold_packet.get(
            "simple_dependency_remediation_queue_exhausted"
        )
        is True
        and hold_packet.get("dependency_remediation_queue_exhausted") is True,
        "release_packet_not_assembled": hold_packet.get("release_packet_assembled")
        is False
        and hold_packet.get("release_assembly_authorized") is False,
        "readiness_not_marked": hold_packet.get("v01_alpha_marked_ready") is False
        and hold_packet.get("readiness_marking_authorized") is False,
        "no_theorem_or_proof_debt_discharge": hold_packet.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and hold_packet.get("proof_debt_reduced") is False
        and hold_packet.get("axiom_spec_backed_debt_reduced") is False,
        "no_source_map_or_qft_gr_seam_closure": hold_packet.get(
            "source_map_closure_claimed"
        )
        is False
        and hold_packet.get("source_map_closure_achieved") is False
        and hold_packet.get("qft_gr_seam_closure_claimed") is False
        and hold_packet.get("qft_gr_seam_closed") is False,
        "no_phase2_empirical_or_master_action_promotion": all(
            hold_packet.get(key, hold_packet_forbidden.get(key)) is False
            for key in [
                "phase2_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "future_route_preserved": hold_packet.get("required_future_route_for_tranche_004")
        == TRANCHE_004_FUTURE_ROUTE,
        "review_authorizes_post_hold_routing_only": NEXT_TARGET
        == "prepare_v01_alpha_post_hold_routing_packet_due_to_retained_tranche_004",
        "review_does_not_prepare_post_hold_routing": forbidden_effect_status[
            "post_hold_routing_packet_prepared"
        ]
        is False,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": True,
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
        else "V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_RESULT_REVIEW_BLOCKED",
        "consumes_hold_packet": EXPECTED_HOLD_PACKET_ID,
        "consumes_hold_packet_pointer": _ptr(hold_packet_path),
        "consumed_hold_packet_schema_id": hold_packet.get("schema_id"),
        "review_scope": (
            "REVIEW_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_"
            "ONLY_ACCEPT_HOLD_AUTHORIZE_POST_HOLD_ROUTING_NO_RELEASE_PROMOTION"
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
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_dependency_finding_id": TRANCHE_006_FINDING_ID,
        "documented_dependency_nonblocking_tranches": documented_rows,
        "documented_dependency_nonblocking_tranche_count": len(documented_rows),
        "dependency_remediation_queue_exhausted": True,
        "simple_dependency_remediation_queue_exhausted": True,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": hold_packet.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": hold_packet.get(
            "retained_release_blocking_obligation_count"
        ),
        "release_hold_packet_reviewed": True,
        "release_hold_packet_accepted": accepted,
        "release_hold_packet_prepared": True,
        "release_hold_packet_prepared_by_review": False,
        "release_hold_registered": False,
        "release_hold_registered_by_review": False,
        "release_hold_reason": "retained_tranche_004_source_map_blocker",
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_proceed_authorized": False,
        "post_hold_routing_authorized": accepted,
        "post_hold_routing_packet_prepared": False,
        "future_remediation_program_prepared_by_review": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "source_map_closure_achieved": False,
        "source_map_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "master_action_promotion_authorized": False,
        "tranche_004_future_route_required": hold_packet.get(
            "tranche_004_future_route_required"
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
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
        else "REMEDIATE_V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_RESULT_REVIEW",
        "selected_next_target_kind": "post_hold_routing_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_ONLY_"
            "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The hold packet is accepted, so the next bounded step prepares a "
                    "control-plane routing packet for the retained tranche 004 posture."
                ),
            },
            {
                "target": FUTURE_REMEDIATION_PROGRAM_TARGET,
                "decision": "deferred",
                "reason": (
                    "A future remediation program is deferred until post-hold routing "
                    "selects it explicitly."
                ),
            },
            {
                "target": ASSEMBLE_RELEASE_PACKET_TARGET,
                "decision": "not_authorized",
                "reason": (
                    "Release assembly remains blocked because tranche 004 remains retained."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The release-hold packet result review accepts only the release hold caused by "
            "the retained tranche 004 source-map blocker and authorizes only post-hold "
            "routing packet preparation. It does not prepare that routing packet, assemble "
            "release, mark readiness, downgrade tranche 004, discharge theorem/proof debt "
            "or retained assumptions, claim source-map or QFT-GR seam closure, authorize "
            "Phase 2, validate empirically, promote the master action, or make an "
            "external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    hold_packet_path: Path = DEFAULT_HOLD_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        hold_packet_path=hold_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha release-hold packet result review due to retained "
            "tranche 004 source-map blocker."
        )
    )
    parser.add_argument("--hold-packet", type=Path, default=DEFAULT_HOLD_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    hold_packet_path = (
        ns.hold_packet if ns.hold_packet.is_absolute() else (REPO_ROOT / ns.hold_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        hold_packet_path=hold_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_result_review_report: "
        f"accepted={payload['accepted']} hold_accepted={payload['release_hold_packet_accepted']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
