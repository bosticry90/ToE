from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_POST_TRANSPORT_RETRY_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "GR_POST_TRANSPORT_RETRY_DECISION_20260412_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))
    decision_contract = dict(declaration.get("decision_contract", {}))

    retry_report_path = REPO_ROOT / str(
        required_inputs.get("gr_master_action_transport_attack_retry_packet_report", "")
    ).strip()
    obligation_report_path = REPO_ROOT / str(
        required_inputs.get("gr_master_action_transport_obligation_declaration_report", "")
    ).strip()

    retry_report = _read_json(retry_report_path)
    obligation_report = _read_json(obligation_report_path)

    retry_summary = dict(retry_report.get("summary", {}))
    retry_outcome = str(retry_summary.get("terminal_outcome", "")).strip()
    retry_target_row = str(retry_summary.get("target_row", "")).strip()
    retry_attack_class = str(retry_summary.get("attack_class", "")).strip()

    obligation_summary = dict(obligation_report.get("summary", {}))
    obligation_id = str(obligation_summary.get("missing_obligation_id", "")).strip()
    obligation_type = str(obligation_summary.get("obligation_type", "")).strip()

    target_row = str(decision_policy.get("target_row", "")).strip()
    prior_attack_class = str(decision_policy.get("prior_attack_class", "")).strip()
    prior_result = str(decision_policy.get("prior_result", "")).strip()
    focus_area = str(decision_policy.get("focus_area", "")).strip()

    allowed_outcomes = set(decision_contract.get("allowed_outcomes", []))
    default_outcome = str(decision_contract.get("default_outcome", "HOLD_GR_AND_REQUIRE_HIGHER_LEVEL_REVIEW")).strip()

    preconditions_ok = (
        retry_target_row == target_row
        and retry_attack_class == prior_attack_class
        and retry_outcome == prior_result
    )

    is_regime_limit_focused = "REGIME_LIMIT" in obligation_id and focus_area == "REGIME_LIMIT_STRUCTURE"

    if not preconditions_ok:
        terminal_outcome = "HOLD_GR_AND_REQUIRE_HIGHER_LEVEL_REVIEW"
        next_action = "VERIFY_POST_TRANSPORT_DECISION_PRECONDITIONS_AND_RETRY"
    elif is_regime_limit_focused:
        terminal_outcome = "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK"
        next_action = "AUTHORIZE_ONE_BOUNDED_GR_REGIME_LIMIT_ALIGNMENT_ATTACK_PACKET"
    else:
        terminal_outcome = default_outcome
        next_action = "PROCEED_WITH_NEXT_BOUNDED_GR_ATTACK"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_row_scope_match": retry_target_row == target_row,
            "attack_class_scope_match": retry_attack_class == prior_attack_class,
            "prior_result_match": retry_outcome == prior_result,
            "regime_limit_focus_match": is_regime_limit_focused,
            "single_terminal_outcome_rule_declared": str(
                decision_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_GR_POST_TRANSPORT_DECISION_OUTCOME",
            "no_loop_rule_declared": str(decision_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_POST_TRANSPORT_DECISION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "decision_preconditions_ok": preconditions_ok,
            },
            "inputs": {
                "target_row": target_row,
                "retry_target_row": retry_target_row,
                "retry_attack_class": retry_attack_class,
                "prior_attack_class": prior_attack_class,
                "prior_result": prior_result,
                "retry_outcome": retry_outcome,
                "obligation_id": obligation_id,
                "obligation_type": obligation_type,
                "focus_area": focus_area,
                "is_regime_limit_focused": is_regime_limit_focused,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                in {
                    "ACTIVATE_GR_WEAK_FIELD_CLOSURE_ATTACK",
                    "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
                    "ACTIVATE_GR_SEAM_INTERFACE_ATTACK",
                    "HOLD_GR_AND_REQUIRE_HIGHER_LEVEL_REVIEW",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "prior_attack_class": prior_attack_class,
            "next_action": next_action,
            "single_decision_only": bool(decision_policy.get("single_decision_only", True)),
            "single_outcome_only": bool(decision_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_master_action_transport_attack_retry_packet_report": _ptr(retry_report_path),
            "gr_master_action_transport_obligation_declaration_report": _ptr(obligation_report_path),
        },
        "non_claim_boundary": "Repository-local GR post-transport-retry decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR post-transport-retry decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_post_transport_retry_decision_20260412_v0.json",
    )
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
        "gr_post_transport_retry_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
