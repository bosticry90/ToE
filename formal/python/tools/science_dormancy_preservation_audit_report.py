from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_DORMANCY_PRESERVATION_AUDIT_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_DORMANCY_PRESERVATION_AUDIT_20260412_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("dormancy_preservation_contract", {}))
    outcome_contract = dict(declaration.get("dormancy_preservation_outcome_contract", {}))

    restart_trigger_path = REPO_ROOT / str(
        required_inputs.get("science_restart_trigger_contract_report", "")
    ).strip()
    controlled_dormancy_path = REPO_ROOT / str(
        required_inputs.get("science_controlled_dormancy_protocol_report", "")
    ).strip()
    playbook_path = REPO_ROOT / str(required_inputs.get("science_dormancy_restart_playbook", "")).strip()

    restart_trigger = _read_json(restart_trigger_path)
    controlled_dormancy = _read_json(controlled_dormancy_path)
    playbook = _read_text(playbook_path)

    restart_summary = dict(restart_trigger.get("summary", {}))
    dormancy_summary = dict(controlled_dormancy.get("summary", {}))

    restart_outcome = str(restart_summary.get("terminal_outcome", "")).strip()
    dormancy_outcome = str(dormancy_summary.get("terminal_outcome", "")).strip()

    lane_reopen_authorized = bool(dormancy_summary.get("lane_specific_reopen_authorized", True))
    new_lane_or_packet_authorized_now = bool(dormancy_summary.get("new_lane_or_packet_authorized_now", True))
    direct_execution_authorized_now = bool(dormancy_summary.get("direct_execution_authorized_now", True))

    required_restart_trigger_outcome = str(contract.get("required_restart_trigger_outcome", "")).strip()
    required_controlled_dormancy_outcome = str(contract.get("required_controlled_dormancy_outcome", "")).strip()
    required_lane_reopen_authorized = bool(contract.get("required_lane_reopen_authorized", False))
    required_new_lane_or_packet_authorized_now = bool(
        contract.get("required_new_lane_or_packet_authorized_now", False)
    )
    required_direct_execution_authorized_now = bool(
        contract.get("required_direct_execution_authorized_now", False)
    )
    required_playbook_phrase = str(contract.get("required_playbook_phrase", "")).strip()
    required_restart_sequence_anchor = str(contract.get("required_restart_sequence_anchor", "")).strip()
    forbid_lane_first_restart_sequencing = bool(contract.get("forbid_lane_first_restart_sequencing", False))

    playbook_phrase_present = required_playbook_phrase in playbook
    restart_sequence_anchor_present = required_restart_sequence_anchor in playbook
    playbook_forbid_lane_first_present = "Do not start restart by selecting a lane." in playbook

    preconditions_ok = (
        restart_outcome == required_restart_trigger_outcome
        and dormancy_outcome == required_controlled_dormancy_outcome
        and lane_reopen_authorized == required_lane_reopen_authorized
        and new_lane_or_packet_authorized_now == required_new_lane_or_packet_authorized_now
        and direct_execution_authorized_now == required_direct_execution_authorized_now
        and playbook_phrase_present
        and restart_sequence_anchor_present
        and (not forbid_lane_first_restart_sequencing or playbook_forbid_lane_first_present)
    )

    contract_shape_ok = all(
        key in contract
        for key in [
            "required_restart_trigger_outcome",
            "required_controlled_dormancy_outcome",
            "required_lane_reopen_authorized",
            "required_new_lane_or_packet_authorized_now",
            "required_direct_execution_authorized_now",
            "required_playbook_phrase",
            "required_restart_sequence_anchor",
            "forbid_lane_first_restart_sequencing",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "DORMANCY_PRESERVATION_AUDIT_EVIDENCE_INCOMPLETE")
    ).strip()

    if not contract_shape_ok:
        terminal_outcome = "HOLD_PENDING_DORMANCY_PRESERVATION_REPAIR"
        next_action = "REPAIR_DORMANCY_PRESERVATION_CONTRACT_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "DORMANCY_PRESERVATION_AUDIT_PASS"
        next_action = "PRESERVE_CONTROLLED_DORMANCY_AND_ENFORCE_TRIGGER_FIRST_RESTART_SEQUENCING"
    else:
        terminal_outcome = "DORMANCY_PRESERVATION_AUDIT_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_DORMANCY_PRESERVATION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "restart_trigger_outcome_match": restart_outcome == required_restart_trigger_outcome,
            "controlled_dormancy_outcome_match": dormancy_outcome == required_controlled_dormancy_outcome,
            "lane_reopen_authorized_match": lane_reopen_authorized == required_lane_reopen_authorized,
            "new_lane_or_packet_authorized_now_match": new_lane_or_packet_authorized_now
            == required_new_lane_or_packet_authorized_now,
            "direct_execution_authorized_now_match": direct_execution_authorized_now
            == required_direct_execution_authorized_now,
            "playbook_trigger_phrase_present": playbook_phrase_present,
            "playbook_restart_sequence_anchor_present": restart_sequence_anchor_present,
            "playbook_forbid_lane_first_present": playbook_forbid_lane_first_present,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_DORMANCY_PRESERVATION_AUDIT_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_DORMANCY_PRESERVATION_AUDIT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "dormancy_preservation_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "restart_trigger_outcome": restart_outcome,
                "required_restart_trigger_outcome": required_restart_trigger_outcome,
                "controlled_dormancy_outcome": dormancy_outcome,
                "required_controlled_dormancy_outcome": required_controlled_dormancy_outcome,
                "lane_reopen_authorized": lane_reopen_authorized,
                "required_lane_reopen_authorized": required_lane_reopen_authorized,
                "new_lane_or_packet_authorized_now": new_lane_or_packet_authorized_now,
                "required_new_lane_or_packet_authorized_now": required_new_lane_or_packet_authorized_now,
                "direct_execution_authorized_now": direct_execution_authorized_now,
                "required_direct_execution_authorized_now": required_direct_execution_authorized_now,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "lane_specific_reopen_authorized": False,
            "new_lane_or_packet_authorized_now": False,
            "direct_execution_authorized_now": False,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_restart_trigger_contract_report": _ptr(restart_trigger_path),
            "science_controlled_dormancy_protocol_report": _ptr(controlled_dormancy_path),
            "science_dormancy_restart_playbook": _ptr(playbook_path),
        },
        "non_claim_boundary": "Repository-local dormancy preservation audit report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate dormancy preservation audit report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_dormancy_preservation_audit_20260412_v0.json",
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
        "science_dormancy_preservation_audit_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
