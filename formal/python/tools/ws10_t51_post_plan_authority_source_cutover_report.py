from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T51_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_REPORT_20260419_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t51_post_plan_authority_source_cutover_20260419_v0.json"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
T50_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json"
MEMO_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_CONSOLIDATION_MEMO_20260418_v0.md"


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
    program_text = _read_text(PROGRAM_PATH)
    state_text = _read_text(STATE_PATH)
    roadmap_text = _read_text(ROADMAP_PATH)
    memo_text = _read_text(MEMO_PATH)
    t50 = _read_json(T50_PATH)

    memo_canonical_ok = all(
        token in memo_text
        for token in [
            "The canonical active control stack is the Phase 3 through Phase 6 bundle completed on 2026-04-18.",
            "When a legacy restart-era surface conflicts with the Phase 3 through Phase 6 stack, the Phase 3 through Phase 6 stack governs.",
            "POST_PLAN_CONSOLIDATION_CANONICAL_POSTURE_v0: PHASE3_TO_PHASE6_CONTROL_STACK_GOVERNS_CURRENT_REPO_READS",
        ]
    )
    memo_restart_historical_ok = all(
        token in memo_text
        for token in [
            "Restart-era authority anchors retained for traceability only:",
            "POST_PLAN_CONSOLIDATION_HISTORICAL_POSTURE_v0: WS10_RESTART_SURFACES_RETAINED_FOR_TRACEABILITY_ONLY",
        ]
    )
    t50_ok = (
        t50.get("summary", {}).get("terminal_outcome") == "WS10_POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_PINNED_NONLIVE_v0"
        and t50.get("summary", {}).get("next_action")
        == "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_BEFORE_ANY_DOWNSTREAM_RECLASSIFICATION"
    )

    state_token = "THEORY_RESTART_T50_POST_PLAN_PHASE_X_STATUS_v0: ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0"
    roadmap_token = "THEORY_RESTART_T50_POST_PLAN_PHASE_X_STATUS_v0: ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0"
    mirrors_ok = state_token in state_text and roadmap_token in roadmap_text
    program_ok = all(
        token in program_text
        for token in [
            "WS10_REMEDIATION_PHASE_X_T50_STATUS_v0: ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0",
            "WS10_REMEDIATION_PHASE_X_T50_ADJUDICATION_v0: POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_PINNED_NONLIVE_v0",
        ]
    )
    next_action = "RUN_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_AGAINST_POST_PLAN_AUTHORITY_CUTOVER"
    all_ok = all([memo_canonical_ok, memo_restart_historical_ok, t50_ok, mirrors_ok, program_ok])
    terminal_outcome = (
        "WS10_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_PINNED_NONLIVE_v0"
        if all_ok
        else "WS10_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_EVIDENCE_INCOMPLETE_v0"
    )

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_t51_post_plan_authority_source_cutover_20260419_v0",
        "status": "ACTIVE_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_NONLIVE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "consolidation_memo_canonical_stack_declared": memo_canonical_ok,
            "consolidation_memo_restart_surfaces_historical_only": memo_restart_historical_ok,
            "t50_alignment_report_present": t50_ok,
            "ws10_program_alignment_present": program_ok,
            "state_and_roadmap_alignment_present": mirrors_ok,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": all_ok,
                "single_outcome_materialized": True,
                "active_authority_stack_single_sourced": all([memo_canonical_ok, memo_restart_historical_ok, t50_ok]),
                "legacy_restart_surfaces_demoted_to_traceability_only": memo_restart_historical_ok,
            },
            "inputs": {
                "t50_terminal_outcome": t50.get("summary", {}).get("terminal_outcome"),
                "t50_next_action": t50.get("summary", {}).get("next_action"),
                "memo_pointer": _ptr(MEMO_PATH),
                "authority_state_pointer": _ptr(STATE_PATH),
                "authority_roadmap_pointer": _ptr(ROADMAP_PATH),
                "authority_program_pointer": _ptr(PROGRAM_PATH),
            },
            "summary": {
                "all_criteria_satisfied": all_ok,
                "phase_status": "COMPLETE" if all_ok else "INCOMPLETE",
                "next_action": next_action if all_ok else "REPAIR_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_EVIDENCE_AND_RERUN",
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "cutover_result": "PHASE3_TO_PHASE6_CONTROL_STACK_GOVERNS_CURRENT_REPO_READS",
            "legacy_restart_status": "WS10_RESTART_SURFACES_RETAINED_FOR_TRACEABILITY_ONLY",
            "next_action": next_action if all_ok else "REPAIR_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_EVIDENCE_AND_RERUN",
        },
        "source_bundle": {
            "consolidation_memo": _ptr(MEMO_PATH),
            "t50_alignment_report": _ptr(T50_PATH),
            "ws10_program": _ptr(PROGRAM_PATH),
            "state": _ptr(STATE_PATH),
            "roadmap": _ptr(ROADMAP_PATH),
        },
        "non_claim_boundary": "This cutover report pins strict repo authority residency only. It does not assert blocker movement, theorem closure, or scientific adequacy.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T51 post-plan authority-source cutover report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    ns = parser.parse_args(argv)

    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"ws10_t51_post_plan_authority_source_cutover_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())