from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_RETRY_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_RETRY_PACKET_20260412_v0.json"
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


def _row_success_count(row_trend: dict[str, Any], target_row: str) -> int:
    counts = dict(dict(row_trend.get("objective_quality", {})).get("inputs", {}).get("row_outcome_counts", {}))
    return int(dict(counts.get(target_row, {})).get("success", 0) or 0)


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    retry_binding = dict(declaration.get("retry_binding", {}))
    ruling_contract = dict(declaration.get("ruling_contract", {}))

    prior_decl_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_attack_packet_declaration", "")
    ).strip()
    prior_report_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_attack_packet_report", "")
    ).strip()
    obligation_report_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_obligation_declaration_report", "")
    ).strip()
    gr_subtarget_report_path = REPO_ROOT / str(required_inputs.get("gr_subtarget_report", "")).strip()
    row_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", "")).strip()
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_report", "")).strip()

    prior_decl = _read_json(prior_decl_path)
    prior_report = _read_json(prior_report_path)
    obligation_report = _read_json(obligation_report_path)
    gr_subtarget_report = _read_json(gr_subtarget_report_path)
    row_trend = _read_json(row_trend_path)
    ledger = _read_json(ledger_path)

    target_row = str(declaration.get("target_row", "")).strip()

    prior_attack_class = str(prior_decl.get("attack_class", "")).strip()
    prior_summary = dict(prior_report.get("summary", {}))
    prior_packet_outcome = str(prior_summary.get("terminal_outcome", "")).strip()
    prior_target_row = str(prior_summary.get("target_row", "")).strip()

    obligation_summary = dict(obligation_report.get("summary", {}))
    obligation_outcome = str(obligation_summary.get("terminal_outcome", "")).strip()
    obligation_id = str(obligation_summary.get("missing_obligation_id", "")).strip()
    retry_justified = bool(obligation_summary.get("retry_justified", False))

    subtarget_inputs = dict(dict(gr_subtarget_report.get("objective_quality", {})).get("inputs", {}))
    theorem_gap_delta = int(subtarget_inputs.get("theorem_gap_delta", 0) or 0)
    target_row_success_incremented = bool(subtarget_inputs.get("target_row_success_count_incremented", False))
    row_success_count = _row_success_count(row_trend, target_row)

    blocker_state_change = str(ledger.get("actual_blocker_state_change", "")).strip()
    blocker_state_token_changed = blocker_state_change not in {"", "NO_DELTA_DETECTED_ROUTE_TO_REWORK"}

    required_prior_packet_outcome = str(retry_binding.get("required_prior_packet_outcome", "")).strip()
    required_obligation_outcome = str(retry_binding.get("required_obligation_outcome", "")).strip()
    required_obligation_id = str(retry_binding.get("required_obligation_id", "")).strip()
    required_attack_class = str(retry_binding.get("required_attack_class", "")).strip()
    required_target_row = str(retry_binding.get("required_target_row", "")).strip()

    preconditions_ok = (
        target_row == required_target_row
        and prior_target_row == required_target_row
        and prior_attack_class == required_attack_class
        and prior_packet_outcome == required_prior_packet_outcome
        and obligation_outcome == required_obligation_outcome
        and obligation_id == required_obligation_id
        and retry_justified
    )

    allowed_outcomes = set(ruling_contract.get("allowed_outcomes", []))
    default_outcome = str(ruling_contract.get("default_outcome", "GR_PATH_FALSIFIED")).strip()

    if not preconditions_ok:
        terminal_outcome = "GR_PATH_FALSIFIED"
        next_action = "STOP_RETRY_AND_RESTORE_RETRY_BINDING_INTEGRITY"
    elif theorem_gap_delta < 0 or target_row_success_incremented or blocker_state_token_changed:
        terminal_outcome = "GR_BLOCKER_MOVED"
        next_action = "PROMOTE_GR_REGIME_LIMIT_ALIGNMENT_AFTER_RETRY_MOVE"
    elif theorem_gap_delta == 0 and not target_row_success_incremented and row_success_count == 0:
        terminal_outcome = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
        next_action = "ESCALATE_STRUCTURE_BEYOND_DECLARED_REGIME_LIMIT_ALIGNMENT_OBLIGATION"
    else:
        terminal_outcome = "GR_VALID_BUT_NONMOVING"
        next_action = "HOLD_GR_REGIME_LIMIT_ALIGNMENT_RETRY_RESULT_AND_RESELECT_IF_NEEDED"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_row_scope_match": target_row == required_target_row == prior_target_row,
            "attack_class_binding_match": prior_attack_class == required_attack_class,
            "prior_packet_outcome_match": prior_packet_outcome == required_prior_packet_outcome,
            "obligation_outcome_match": obligation_outcome == required_obligation_outcome,
            "obligation_id_match": obligation_id == required_obligation_id,
            "retry_justified": retry_justified,
            "single_terminal_outcome_rule_declared": str(
                ruling_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_GR_REGIME_LIMIT_ALIGNMENT_RETRY_OUTCOME",
            "no_loop_rule_declared": str(ruling_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_REGIME_LIMIT_ALIGNMENT_RETRY_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "retry_binding_preconditions_ok": preconditions_ok,
            },
            "inputs": {
                "target_row": target_row,
                "prior_target_row": prior_target_row,
                "prior_attack_class": prior_attack_class,
                "prior_packet_outcome": prior_packet_outcome,
                "required_prior_packet_outcome": required_prior_packet_outcome,
                "obligation_outcome": obligation_outcome,
                "required_obligation_outcome": required_obligation_outcome,
                "obligation_id": obligation_id,
                "required_obligation_id": required_obligation_id,
                "retry_justified": retry_justified,
                "theorem_gap_delta": theorem_gap_delta,
                "target_row_success_incremented": target_row_success_incremented,
                "row_success_count": row_success_count,
                "blocker_state_change": blocker_state_change,
                "blocker_state_token_changed": blocker_state_token_changed,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                in {
                    "GR_BLOCKER_MOVED",
                    "GR_VALID_BUT_NONMOVING",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "attack_class": required_attack_class,
            "bound_obligation_id": required_obligation_id,
            "next_action": next_action,
            "single_retry_only": bool(retry_binding.get("single_retry_only", True)),
            "single_ruling_only": bool(retry_binding.get("single_ruling_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_regime_limit_alignment_attack_packet_declaration": _ptr(prior_decl_path),
            "gr_regime_limit_alignment_attack_packet_report": _ptr(prior_report_path),
            "gr_regime_limit_alignment_obligation_declaration_report": _ptr(obligation_report_path),
            "gr_subtarget_report": _ptr(gr_subtarget_report_path),
            "row_outcome_trend_report": _ptr(row_trend_path),
            "ledger_report": _ptr(ledger_path),
        },
        "non_claim_boundary": "Repository-local GR regime-limit alignment retry packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR regime-limit alignment attack retry packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_regime_limit_alignment_attack_retry_packet_20260412_v0.json",
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
        "gr_regime_limit_alignment_attack_retry_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
