from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_FINAL_INTEGRATION_REVIEW_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_FINAL_INTEGRATION_REVIEW_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_final_integration_review_20260418_v0.json"
)


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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    phase3_path = REPO_ROOT / str(required_inputs.get("post_plan_qm_theorem_gap_tranche_report", "")).strip()
    phase4_path = REPO_ROOT / str(required_inputs.get("post_plan_seam_reroute_reassessment_report", "")).strip()
    phase5_path = REPO_ROOT / str(required_inputs.get("post_plan_master_action_reevaluation_report", "")).strip()
    integration_gate_path = REPO_ROOT / str(required_inputs.get("final_nonclaim_integration_promotion_gate_report", "")).strip()

    phase3 = _read_json(phase3_path)
    phase4 = _read_json(phase4_path)
    phase5 = _read_json(phase5_path)
    integration_gate = _read_json(integration_gate_path)

    advancement_movement_detected = (
        phase3.get("summary", {}).get("terminal_outcome") == "POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_AND_PROMOTED"
        or phase4.get("summary", {}).get("terminal_outcome") == "POST_PLAN_SEAM_REROUTE_REASSESSMENT_MATERIALIZED"
        or phase5.get("summary", {}).get("terminal_outcome") == "POST_PLAN_MASTER_ACTION_REEVALUATION_MATERIALIZED"
    )
    integration_gate_ok = integration_gate.get("summary", {}).get("terminal_outcome") == "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_SATISFIED"

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_FINAL_INTEGRATION_REVIEW_EVIDENCE_INCOMPLETE")).strip()

    if not integration_gate_ok:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_FINAL_INTEGRATION_REVIEW_REPAIR"
        next_action = "RESTORE_POST_PLAN_FINAL_INTEGRATION_INPUT_SHAPE_AND_RERUN"
    elif advancement_movement_detected:
        terminal_outcome = "POST_PLAN_FINAL_INTEGRATION_REVIEW_ADVANCEMENT_ELIGIBLE"
        next_action = "EVALUATE_WHETHER_NEW_ADVANCEMENT_JUSTIFIES_UPDATED_INTEGRATION_POSTURE"
    else:
        terminal_outcome = "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT"
        next_action = "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_BEFORE_ANY_DOWNSTREAM_RECLASSIFICATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase3_report_present": bool(phase3),
            "phase4_report_present": bool(phase4),
            "phase5_report_present": bool(phase5),
            "canonical_nonclaim_integration_gate_satisfied": integration_gate_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_FINAL_INTEGRATION_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_FINAL_INTEGRATION_REVIEW_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "integration_advancement_only_after_post_plan_movement": (terminal_outcome != "POST_PLAN_FINAL_INTEGRATION_REVIEW_ADVANCEMENT_ELIGIBLE") or advancement_movement_detected,
            },
            "inputs": {
                "advancement_movement_detected": advancement_movement_detected,
                "phase3_terminal_outcome": phase3.get("summary", {}).get("terminal_outcome"),
                "phase4_terminal_outcome": phase4.get("summary", {}).get("terminal_outcome"),
                "phase5_terminal_outcome": phase5.get("summary", {}).get("terminal_outcome"),
                "canonical_integration_gate_terminal_outcome": integration_gate.get("summary", {}).get("terminal_outcome"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "advancement_movement_detected": advancement_movement_detected,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_qm_theorem_gap_tranche_report": _ptr(phase3_path),
            "post_plan_seam_reroute_reassessment_report": _ptr(phase4_path),
            "post_plan_master_action_reevaluation_report": _ptr(phase5_path),
            "final_nonclaim_integration_promotion_gate_report": _ptr(integration_gate_path),
        },
        "non_claim_boundary": "Repository-local post-plan final integration review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan final integration review report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"post_plan_final_integration_review_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())