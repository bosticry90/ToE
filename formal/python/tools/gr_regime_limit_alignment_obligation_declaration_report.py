from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
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
    obligation_policy = dict(declaration.get("obligation_policy", {}))
    declaration_contract = dict(declaration.get("declaration_contract", {}))

    packet_report_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_attack_packet_report", "")
    ).strip()
    decision_path = REPO_ROOT / str(
        required_inputs.get("gr_post_transport_retry_decision_report", "")
    ).strip()

    packet_report = _read_json(packet_report_path)
    decision_report = _read_json(decision_path)

    packet_summary = dict(packet_report.get("summary", {}))
    decision_summary = dict(decision_report.get("summary", {}))

    packet_outcome = str(packet_summary.get("terminal_outcome", "")).strip()
    packet_target_row = str(packet_summary.get("target_row", "")).strip()
    decision_outcome = str(decision_summary.get("terminal_outcome", "")).strip()
    decision_target_row = str(decision_summary.get("target_row", "")).strip()

    target_row = str(obligation_policy.get("target_row", "")).strip()
    obligation_id = str(obligation_policy.get("missing_obligation_id", "")).strip()
    obligation_statement = str(obligation_policy.get("missing_obligation_statement", "")).strip()
    obligation_type = str(obligation_policy.get("obligation_type", "")).strip().upper()
    scope_violation_detected = bool(obligation_policy.get("scope_violation_detected", False))
    requires_higher_level_policy = bool(obligation_policy.get("requires_higher_level_policy", False))
    obligation_justified = bool(obligation_policy.get("obligation_justified", False))
    obligation_declared = bool(obligation_policy.get("obligation_declared", False))

    scope_match = packet_target_row == target_row == decision_target_row
    packet_requires_obligation = packet_outcome == "GR_REGIME_LIMIT_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE"
    decision_matches_alignment = decision_outcome == "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK"
    obligation_type_allowed = obligation_type in {"THEOREM_LINKED", "PLACEHOLDER", "SPECULATIVE"}

    allowed_outcomes = set(declaration_contract.get("allowed_outcomes", []))
    default_outcome = str(
        declaration_contract.get("default_outcome", "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED")
    ).strip()

    if scope_violation_detected or not scope_match:
        terminal_outcome = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_OUT_OF_SCOPE"
        next_action = "DO_NOT_RETRY_PACKET_AND_RESTORE_SCOPE_ALIGNMENT"
    elif requires_higher_level_policy:
        terminal_outcome = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_REQUIRES_HIGHER_LEVEL_POLICY"
        next_action = "DEFINE_HIGHER_LEVEL_POLICY_SURFACE_BEFORE_ANY_RETRY"
    elif (
        packet_requires_obligation
        and decision_matches_alignment
        and obligation_justified
        and obligation_declared
        and obligation_type_allowed
        and bool(obligation_id)
        and bool(obligation_statement)
    ):
        terminal_outcome = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED"
        next_action = "AUTHORIZE_ONE_BOUNDED_RETRY_OF_GR_REGIME_LIMIT_ALIGNMENT_PACKET"
    else:
        terminal_outcome = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"
        next_action = "HOLD_GR_REGIME_LIMIT_ALIGNMENT_PATH_UNTIL_JUSTIFICATION_IS_EXPLICIT"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_requires_alignment_obligation": packet_requires_obligation,
            "decision_matches_alignment_attack": decision_matches_alignment,
            "target_row_scope_match": scope_match,
            "single_terminal_outcome_rule_declared": str(
                declaration_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_OUTCOME",
            "no_loop_rule_declared": str(declaration_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "obligation_type_allowed": obligation_type_allowed,
            },
            "inputs": {
                "packet_outcome": packet_outcome,
                "decision_outcome": decision_outcome,
                "target_row": target_row,
                "packet_target_row": packet_target_row,
                "decision_target_row": decision_target_row,
                "missing_obligation_id": obligation_id,
                "obligation_type": obligation_type,
                "scope_violation_detected": scope_violation_detected,
                "requires_higher_level_policy": requires_higher_level_policy,
                "obligation_justified": obligation_justified,
                "obligation_declared": obligation_declared,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                in {
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_REQUIRES_HIGHER_LEVEL_POLICY",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "missing_obligation_id": obligation_id,
            "obligation_type": obligation_type,
            "next_action": next_action,
            "retry_justified": terminal_outcome == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_regime_limit_alignment_attack_packet_report": _ptr(packet_report_path),
            "gr_post_transport_retry_decision_report": _ptr(decision_path),
        },
        "non_claim_boundary": "Repository-local GR regime-limit alignment obligation declaration report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR regime-limit alignment obligation declaration report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
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
        "gr_regime_limit_alignment_obligation_declaration_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
