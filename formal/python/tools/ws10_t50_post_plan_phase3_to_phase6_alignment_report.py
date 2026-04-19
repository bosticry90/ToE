from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T50_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json"
POST_PLAN_PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
PHASE3_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_qm_first_theorem_gap_tranche_20260418_v0.json"
PHASE4_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_seam_reroute_reassessment_20260418_v0.json"
PHASE5_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_master_action_reevaluation_20260418_v0.json"
PHASE6_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_final_integration_review_20260418_v0.json"


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    program_text = _read_text(POST_PLAN_PROGRAM_PATH)
    phase3 = _read_json(PHASE3_PATH)
    phase4 = _read_json(PHASE4_PATH)
    phase5 = _read_json(PHASE5_PATH)
    phase6 = _read_json(PHASE6_PATH)

    phase3_ok = (
        phase3.get("summary", {}).get("terminal_outcome") == "POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED"
        and phase3.get("summary", {}).get("target_row_id") == "ROW-PILLAR-QM-001"
        and phase3.get("summary", {}).get("next_action") == "RETAIN_CURRENT_SEAM_AND_MASTER_ACTION_CLASSES_AND_SELECT_NEXT_THEOREM_GAP_TRANCHE"
    )
    phase4_ok = (
        phase4.get("summary", {}).get("terminal_outcome") == "POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT"
        and phase4.get("summary", {}).get("next_action") == "PRESERVE_CURRENT_SEAM_CLASSES_AND_SKIP_REROUTE"
    )
    phase5_ok = (
        phase5.get("summary", {}).get("terminal_outcome") == "POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT"
        and phase5.get("summary", {}).get("next_action") == "KEEP_MASTER_ACTION_FROZEN_AS_SUPPORT_ONLY"
    )
    phase6_ok = (
        phase6.get("summary", {}).get("terminal_outcome") == "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT"
        and phase6.get("summary", {}).get("next_action")
        == "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_BEFORE_ANY_DOWNSTREAM_RECLASSIFICATION"
    )
    program_tokens_ok = all(
        token in program_text
        for token in [
            "POST_PLAN_PHYSICS_ADVANCEMENT_PHASE3_QM_TRANCHE_v0: POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED",
            "POST_PLAN_PHYSICS_ADVANCEMENT_PHASE4_SEAM_REROUTE_v0: POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
            "POST_PLAN_PHYSICS_ADVANCEMENT_PHASE5_MASTER_ACTION_v0: POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
            "POST_PLAN_PHYSICS_ADVANCEMENT_PHASE6_FINAL_INTEGRATION_v0: POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT",
            "POST_PLAN_PHYSICS_ADVANCEMENT_NEXT_ACTION_v0: EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_WITH_POST_CASCADE_HOLD_RECORDED",
        ]
    )

    all_ok = all([phase3_ok, phase4_ok, phase5_ok, phase6_ok, program_tokens_ok])
    terminal_outcome = (
        "WS10_POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_PINNED_NONLIVE_v0"
        if all_ok
        else "WS10_POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_INCOMPLETE_v0"
    )

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0",
        "status": "ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase3_qm_tranche_materialized": phase3_ok,
            "phase4_seam_reroute_hold_materialized": phase4_ok,
            "phase5_master_action_hold_materialized": phase5_ok,
            "phase6_final_integration_hold_materialized": phase6_ok,
            "post_plan_program_tokens_present": program_tokens_ok,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": all_ok,
                "no_new_blocker_closure_claimed": True,
                "no_downstream_reclassification_without_movement": phase4_ok and phase5_ok and phase6_ok,
                "single_outcome_materialized": True,
            },
            "inputs": {
                "phase3_target_row": phase3.get("summary", {}).get("target_row_id"),
                "phase3_terminal_outcome": phase3.get("summary", {}).get("terminal_outcome"),
                "phase4_terminal_outcome": phase4.get("summary", {}).get("terminal_outcome"),
                "phase5_terminal_outcome": phase5.get("summary", {}).get("terminal_outcome"),
                "phase6_terminal_outcome": phase6.get("summary", {}).get("terminal_outcome"),
                "phase6_next_action": phase6.get("summary", {}).get("next_action"),
                "program_level_next_action": "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_WITH_POST_CASCADE_HOLD_RECORDED",
            },
            "summary": {
                "all_criteria_satisfied": all_ok,
                "phase_status": "COMPLETE" if all_ok else "INCOMPLETE",
                "next_action": phase6.get("summary", {}).get(
                    "next_action",
                    "REPAIR_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_AND_RERUN",
                ),
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "post_plan_program": _ptr(POST_PLAN_PROGRAM_PATH),
            "phase3_terminal_outcome": phase3.get("summary", {}).get("terminal_outcome"),
            "phase4_terminal_outcome": phase4.get("summary", {}).get("terminal_outcome"),
            "phase5_terminal_outcome": phase5.get("summary", {}).get("terminal_outcome"),
            "phase6_terminal_outcome": phase6.get("summary", {}).get("terminal_outcome"),
            "next_action": phase6.get("summary", {}).get(
                "next_action",
                "REPAIR_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_AND_RERUN",
            ),
            "active_theorem_gap_row": "ROW-PILLAR-QM-001",
        },
        "source_bundle": {
            "post_plan_program": _ptr(POST_PLAN_PROGRAM_PATH),
            "phase3_qm_tranche_report": _ptr(PHASE3_PATH),
            "phase4_seam_reroute_report": _ptr(PHASE4_PATH),
            "phase5_master_action_report": _ptr(PHASE5_PATH),
            "phase6_final_integration_report": _ptr(PHASE6_PATH),
        },
        "non_claim_boundary": "This alignment report records already-materialized post-plan phase 3 through phase 6 outcomes in the active WS-10 chain. It does not add new blocker movement or scientific adequacy claims.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T50 post-plan phase3-to-phase6 alignment report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    ns = parser.parse_args(argv)

    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"ws10_t50_post_plan_phase3_to_phase6_alignment_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())