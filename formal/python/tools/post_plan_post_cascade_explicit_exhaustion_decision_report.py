from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _maybe_relpath(raw: Any) -> str | None:
    value = str(raw).strip() if raw is not None else ""
    return value or None


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("decision_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    post_cascade_path = REPO_ROOT / str(required_inputs.get("post_plan_post_cascade_closure_review_report", "")).strip()
    qft_path = REPO_ROOT / str(required_inputs.get("post_plan_qft_theorem_gap_completion_tranche_report", "")).strip()
    em_path = REPO_ROOT / str(required_inputs.get("post_plan_em_theorem_gap_completion_tranche_report", "")).strip()
    sr_path = REPO_ROOT / str(required_inputs.get("post_plan_sr_theorem_gap_completion_tranche_report", "")).strip()
    wrapper_path = REPO_ROOT / str(required_inputs.get("post_plan_program_state_conversion_review_wrapper_report", "")).strip()

    post_cascade_report = _read_json(post_cascade_path)
    qft_report = _read_json(qft_path)
    em_report = _read_json(em_path)
    sr_report = _read_json(sr_path)
    wrapper_report = _read_json(wrapper_path)

    successor_decl_rel = _maybe_relpath(policy.get("new_declared_successor_declaration"))
    successor_gate_rel = _maybe_relpath(policy.get("new_declared_successor_gate"))
    successor_decl_path = REPO_ROOT / successor_decl_rel if successor_decl_rel else None
    successor_gate_path = REPO_ROOT / successor_gate_rel if successor_gate_rel else None
    successor_declared = bool(successor_decl_path and successor_decl_path.exists()) and (
        successor_gate_path is None or successor_gate_path.exists()
    )

    post_cascade_ok = (
        post_cascade_report.get("summary", {}).get("terminal_outcome")
        == str(policy.get("required_post_cascade_outcome", "")).strip()
    )
    qft_ok = qft_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_qft_outcome", "")).strip()
    em_ok = em_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_em_outcome", "")).strip()
    sr_ok = sr_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_sr_outcome", "")).strip()
    wrapper_ok = (
        wrapper_report.get("summary", {}).get("terminal_outcome")
        == str(policy.get("required_wrapper_outcome", "")).strip()
        and wrapper_report.get("summary", {}).get("next_action")
        == str(policy.get("required_wrapper_next_action", "")).strip()
    )

    current_family_scope = str(policy.get("required_current_family_scope", "")).strip()
    current_family_consumed = all([post_cascade_ok, qft_ok, em_ok, sr_ok, wrapper_ok])

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get(
            "default_outcome",
            "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not all([post_cascade_report, qft_report, em_report, sr_report, wrapper_report]):
        terminal_outcome = "HOLD_PENDING_POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REPAIR"
        next_action = "RESTORE_POST_CASCADE_EXHAUSTION_DECISION_INPUTS_AND_RERUN"
    elif current_family_consumed and successor_declared:
        terminal_outcome = "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REOPENED_BY_NEW_DECLARED_SUCCESSOR"
        next_action = str(policy.get("successor_next_action_if_declared", "EXECUTE_DECLARED_SUCCESSOR_FAMILY_ONCE")).strip()
    elif current_family_consumed:
        terminal_outcome = "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY"
        next_action = "AUTHOR_NEW_DECLARED_SUCCESSOR_FAMILY_OR_ACCEPT_TERMINAL_EXHAUSTION_READ"
    else:
        terminal_outcome = "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_CASCADE_EXHAUSTION_DECISION_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "post_cascade_bounded_hold_recorded": post_cascade_ok,
            "qft_nonmoving_tranche_recorded": qft_ok,
            "em_nonmoving_tranche_recorded": em_ok,
            "sr_nonmoving_tranche_recorded": sr_ok,
            "conversion_wrapper_reuse_recorded": wrapper_ok,
            "successor_reopen_rule_declared": str(policy.get("successor_reopen_rule", "")).strip()
            == "ONLY_IF_NEW_DECLARED_SUCCESSOR_POINTER_IS_PRESENT_AND_MACHINE_PINNED",
            "lookalike_row_no_loop_rule_declared": str(policy.get("lookalike_row_no_loop_rule", "")).strip()
            == "NO_ADDITIONAL_LOOKALIKE_THEOREM_GAP_ROW_WITHOUT_NEW_DECLARED_SUCCESSOR_FAMILY",
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "exhaustion_only_after_full_nonmoving_chain": (
                    terminal_outcome != "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY"
                )
                or current_family_consumed,
                "reopen_only_if_new_successor_declared": (
                    terminal_outcome != "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_REOPENED_BY_NEW_DECLARED_SUCCESSOR"
                )
                or successor_declared,
            },
            "inputs": {
                "current_family_scope": current_family_scope,
                "post_cascade_outcome": post_cascade_report.get("summary", {}).get("terminal_outcome"),
                "qft_outcome": qft_report.get("summary", {}).get("terminal_outcome"),
                "em_outcome": em_report.get("summary", {}).get("terminal_outcome"),
                "sr_outcome": sr_report.get("summary", {}).get("terminal_outcome"),
                "wrapper_outcome": wrapper_report.get("summary", {}).get("terminal_outcome"),
                "wrapper_next_action": wrapper_report.get("summary", {}).get("next_action"),
                "successor_declared": successor_declared,
                "successor_declaration": successor_decl_rel,
                "successor_gate": successor_gate_rel,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "current_family_scope": current_family_scope,
            "current_family_consumed": current_family_consumed,
            "successor_declared": successor_declared,
            "successor_declaration": successor_decl_rel,
            "successor_gate": successor_gate_rel,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_post_cascade_closure_review_report": _ptr(post_cascade_path),
            "post_plan_qft_theorem_gap_completion_tranche_report": _ptr(qft_path),
            "post_plan_em_theorem_gap_completion_tranche_report": _ptr(em_path),
            "post_plan_sr_theorem_gap_completion_tranche_report": _ptr(sr_path),
            "post_plan_program_state_conversion_review_wrapper_report": _ptr(wrapper_path),
            "new_declared_successor_declaration": successor_decl_rel,
            "new_declared_successor_gate": successor_gate_rel,
        },
        "non_claim_boundary": "Repository-local post-cascade explicit exhaustion decision only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan post-cascade explicit exhaustion decision report."
    )
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
    print(
        "post_plan_post_cascade_explicit_exhaustion_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())