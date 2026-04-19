from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_REPORT_20260419_v0"
FAMILY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "sandbox_promotion_boundary_enforcement_family_20260419_v0.json"
)
SANDBOX_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md"
PROMOTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
AUTHORITY_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md"
GOVERNED_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json"
POST_PILOT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


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


def build_report(*, captured_at_utc: str | None) -> dict[str, Any]:
    family_text = _read_text(FAMILY_PATH)
    sandbox_text = _read_text(SANDBOX_POLICY_PATH)
    promotion_text = _read_text(PROMOTION_POLICY_PATH)
    matrix_text = _read_text(AUTHORITY_MATRIX_PATH)
    governed_report = _read_json(GOVERNED_REPORT_PATH)
    post_pilot_report = _read_json(POST_PILOT_REPORT_PATH)
    state_text = _read_text(STATE_PATH)
    roadmap_text = _read_text(ROADMAP_PATH)

    family_gate_paths = [
        "formal/python/tests/test_sandbox_promotion_lane_policy_gate.py",
        "formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py",
        "formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py",
        "formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
        "formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py",
        "formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
    ]

    mirror_tokens = [
        "SANDBOX_PROMOTION_PHASE5_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE5_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_TOOL_v0: formal/python/tools/sandbox_promotion_boundary_enforcement_family_report.py",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_v0: formal/output/reports/sandbox_promotion_boundary_enforcement_family_20260419_v0.json",
        "SANDBOX_PROMOTION_PHASE5_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE5_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDARY_ENFORCEMENT_FAMILY_AND_FAIL_CLOSED_CLOSEOUT_GATE_PINNED",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    ]

    criteria = {
        "family_surface_tokens_present": all(
            token in family_text
            for token in (
                "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
                "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_SCOPE_v0: POLICY_SPLIT_PLUS_SCHEMA_PAYLOAD_PLUS_GOVERNED_AUDIT_PLUS_AUTHORITY_CUTOVER_PLUS_POST_PILOT_NONWIDENED_BOUNDARY",
                "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_GATES_v0: LANE_POLICY_PLUS_PHASE2_PHASE4_PLUS_PHASE2_PHASE6_PLUS_AUTHORITY_CUTOVER_PLUS_PHASE7_PHASE3_PLUS_PHASE5_CLOSEOUT",
                "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAIL_CLOSED_RULE_v0: ANY_MISSING_BOUNDARY_SURFACE_GATE_POINTER_OR_NONWIDENED_HOLD_DRIFT_BLOCKS_PHASE5_CLOSEOUT",
            )
        ),
        "family_gate_pointers_present": all(path_ref in family_text for path_ref in family_gate_paths),
        "sandbox_boundary_tokens_present": all(
            token in sandbox_text
            for token in (
                "SANDBOX_PHYSICS_LANE_BOUNDARY_v0: RESULTS_STAY_SANDBOX_ONLY_UNTIL_PROMOTION_GATE_SATISFIED",
                "SANDBOX_PHYSICS_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
                "SANDBOX_PHYSICS_LANE_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
            )
        ),
        "promotion_boundary_tokens_present": all(
            token in promotion_text
            for token in (
                "PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW",
                "PROMOTION_GOVERNANCE_LANE_MUTATION_PROTOCOL_v0: formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
                "PROMOTION_GOVERNANCE_LANE_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
                "PROMOTION_GOVERNANCE_LANE_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
                "PROMOTION_GOVERNANCE_LANE_BOUNDARY_ENFORCEMENT_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
            )
        ),
        "authority_cutover_tokens_present": all(
            token in matrix_text
            for token in (
                "SANDBOX_PROMOTION_AUTHORITY_MATRIX_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
                "SANDBOX_PROMOTION_AUTHORITY_CUTOVER_RULE_v0: SANDBOX_SURFACES_OWN_SANDBOX_OUTPUT_AUTHORITY_PROMOTION_SURFACES_OWN_CANONICAL_MUTATION_AUTHORITY",
                "SANDBOX_PROMOTION_AUTHORITY_FAIL_CLOSED_RULE_v0: MISSING_OWNER_OR_PARITY_OR_GATE_POINTER_BLOCKS_CUTOVER",
            )
        ),
        "governed_review_hold_blocks_mutation": governed_report.get("summary", {}).get("terminal_outcome")
        == "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED"
        and governed_report.get("summary", {}).get("canonical_mutation_emitted") is False,
        "post_pilot_nonwidened_boundary_present": post_pilot_report.get("summary", {}).get("post_pilot_decision")
        == "RETAIN_BOUNDED_PILOT_NONWIDENED_AFTER_GOVERNED_HOLD"
        and post_pilot_report.get("summary", {}).get("pilot_disposition") == "HOLD_NONWIDENED",
        "mirror_phase5_complete_tokens_present": all(token in state_text and token in roadmap_text for token in mirror_tokens),
    }

    all_criteria_satisfied = all(criteria.values())
    next_action = (
        "ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK"
        if all_criteria_satisfied
        else "REPAIR_SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_SURFACES_AND_RERUN"
    )
    closeout_status = (
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_COMPLETE"
        if all_criteria_satisfied
        else "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_INCOMPLETE"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": {
                "all_family_criteria_satisfied": all_criteria_satisfied,
                "governed_hold_preserved": criteria["governed_review_hold_blocks_mutation"],
                "nonwidened_post_pilot_boundary_preserved": criteria["post_pilot_nonwidened_boundary_present"],
                "mirror_completion_state_present": criteria["mirror_phase5_complete_tokens_present"],
            },
            "summary": {
                "all_criteria_satisfied": all_criteria_satisfied,
                "phase_status": "COMPLETE" if all_criteria_satisfied else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "closeout_status": closeout_status,
            "governed_terminal_outcome": governed_report.get("summary", {}).get("terminal_outcome"),
            "post_pilot_decision": post_pilot_report.get("summary", {}).get("post_pilot_decision"),
            "next_action": next_action,
        },
        "source_bundle": {
            "family_surface": _ptr(FAMILY_PATH),
            "sandbox_policy": _ptr(SANDBOX_POLICY_PATH),
            "promotion_policy": _ptr(PROMOTION_POLICY_PATH),
            "authority_matrix": _ptr(AUTHORITY_MATRIX_PATH),
            "governed_review_report": _ptr(GOVERNED_REPORT_PATH),
            "post_pilot_decision_report": _ptr(POST_PILOT_REPORT_PATH),
            "state_mirror": _ptr(STATE_PATH),
            "roadmap_mirror": _ptr(ROADMAP_PATH),
        },
        "non_claim_boundary": "Repository-local boundary-enforcement closeout report only; no widening, scientific adequacy, or canonical mutation claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the sandbox-promotion boundary-enforcement family closeout report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "sandbox_promotion_boundary_enforcement_family_report: "
        f"status={payload['summary']['closeout_status']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())