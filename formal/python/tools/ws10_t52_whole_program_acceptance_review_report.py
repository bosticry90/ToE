from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T52_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_REPORT_20260419_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t52_whole_program_acceptance_review_20260419_v0.json"
T51_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t51_post_plan_authority_source_cutover_20260419_v0.json"
T50_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json"
CHECKPOINT_LADDER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "checkpoint_ladder_acceptance_summary_v0.json"
DUAL_TRACK_CUTOVER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "dual_track_cutover_report_v0.json"
FINAL_GATE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "final_nonclaim_integration_promotion_gate_20260418_v0.json"
POST_PLAN_PHASE6_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_final_integration_review_20260418_v0.json"


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
    t51 = _read_json(T51_PATH)
    t50 = _read_json(T50_PATH)
    ladder = _read_json(CHECKPOINT_LADDER_PATH)
    cutover = _read_json(DUAL_TRACK_CUTOVER_PATH)
    final_gate = _read_json(FINAL_GATE_PATH)
    post_plan_phase6 = _read_json(POST_PLAN_PHASE6_PATH)

    t51_ok = t51.get("summary", {}).get("terminal_outcome") == "WS10_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_PINNED_NONLIVE_v0"
    t50_ok = t50.get("summary", {}).get("terminal_outcome") == "WS10_POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_PINNED_NONLIVE_v0"
    ladder_ok = (
        ladder.get("failed") is False
        and all(step.get("status") == "PASSED" for step in ladder.get("step_results", []))
        and any(step.get("key") == "full_governance_suite" and step.get("status") == "PASSED" for step in ladder.get("step_results", []))
    )
    cutover_ok = (
        cutover.get("cutover_readiness", {}).get("overall_pass") is True
        and cutover.get("measurement_policy", {}).get("measured_mode_satisfied") is True
    )
    final_gate_ok = final_gate.get("summary", {}).get("terminal_outcome") == "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_SATISFIED"
    post_plan_phase6_ok = (
        post_plan_phase6.get("summary", {}).get("terminal_outcome")
        == "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT"
        and post_plan_phase6.get("summary", {}).get("advancement_movement_detected") is False
    )

    acceptance_green = all([ladder_ok, cutover_ok, final_gate_ok])
    all_ok = all([t51_ok, t50_ok, acceptance_green, post_plan_phase6_ok])
    terminal_outcome = (
        "WS10_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT_v0"
        if all_ok
        else "WS10_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_EVIDENCE_INCOMPLETE_v0"
    )
    next_action = "KEEP_PHASE6_HELD_AND_REQUIRE_NEW_BLOCKER_MOVEMENT_BEFORE_WHOLE_PROGRAM_ACCEPT_OR_REJECT_CLOSEOUT"

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_t52_whole_program_acceptance_review_20260419_v0",
        "status": "ACTIVE_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_NONLIVE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "t51_authority_cutover_pinned": t51_ok,
            "t50_phase_chain_alignment_pinned": t50_ok,
            "checkpoint_ladder_acceptance_green": ladder_ok,
            "dual_track_cutover_acceptance_green": cutover_ok,
            "canonical_final_nonclaim_gate_satisfied": final_gate_ok,
            "post_plan_phase6_hold_still_declared": post_plan_phase6_ok,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": all_ok,
                "single_outcome_materialized": True,
                "broad_acceptance_green_but_no_post_plan_advancement_movement": acceptance_green and post_plan_phase6_ok,
                "accept_or_reject_not_promoted_without_blocker_movement": post_plan_phase6_ok,
            },
            "inputs": {
                "t51_terminal_outcome": t51.get("summary", {}).get("terminal_outcome"),
                "t50_terminal_outcome": t50.get("summary", {}).get("terminal_outcome"),
                "checkpoint_ladder_failed": ladder.get("failed"),
                "dual_track_cutover_overall_pass": cutover.get("cutover_readiness", {}).get("overall_pass"),
                "canonical_final_gate_outcome": final_gate.get("summary", {}).get("terminal_outcome"),
                "post_plan_phase6_outcome": post_plan_phase6.get("summary", {}).get("terminal_outcome"),
                "advancement_movement_detected": post_plan_phase6.get("summary", {}).get("advancement_movement_detected"),
            },
            "summary": {
                "all_criteria_satisfied": all_ok,
                "phase_status": "COMPLETE" if all_ok else "INCOMPLETE",
                "next_action": next_action if all_ok else "REPAIR_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_EVIDENCE_AND_RERUN",
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "acceptance_stack_status": "GREEN_BUT_NONPROMOTION" if all_ok else "EVIDENCE_INCOMPLETE",
            "post_plan_phase6_outcome": post_plan_phase6.get("summary", {}).get("terminal_outcome"),
            "next_action": next_action if all_ok else "REPAIR_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_EVIDENCE_AND_RERUN",
        },
        "source_bundle": {
            "t51_authority_cutover_report": _ptr(T51_PATH),
            "t50_phase_alignment_report": _ptr(T50_PATH),
            "checkpoint_ladder_acceptance_summary": _ptr(CHECKPOINT_LADDER_PATH),
            "dual_track_cutover_report": _ptr(DUAL_TRACK_CUTOVER_PATH),
            "final_nonclaim_integration_gate": _ptr(FINAL_GATE_PATH),
            "post_plan_final_integration_review": _ptr(POST_PLAN_PHASE6_PATH),
        },
        "non_claim_boundary": "This whole-program acceptance review binds existing authority and acceptance surfaces only. It does not assert scientific adequacy or override the post-plan Phase 6 hold without new blocker movement.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T52 whole-program acceptance review report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    ns = parser.parse_args(argv)

    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"ws10_t52_whole_program_acceptance_review_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())