from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_20260412_v0.json"
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
    contract = dict(declaration.get("controlled_dormancy_contract", {}))
    outcome_contract = dict(declaration.get("controlled_dormancy_outcome_contract", {}))

    restart_trigger_path = REPO_ROOT / str(
        required_inputs.get("science_restart_trigger_contract_report", "")
    ).strip()
    post_z_path = REPO_ROOT / str(
        required_inputs.get("science_post_phase_z_frontier_decision_report", "")
    ).strip()
    summary_doc_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_stop_state_summary_doc", "")
    ).strip()

    restart_trigger = _read_json(restart_trigger_path)
    post_z = _read_json(post_z_path)
    summary_doc = _read_text(summary_doc_path)

    restart_trigger_summary = dict(restart_trigger.get("summary", {}))
    post_z_summary = dict(post_z.get("summary", {}))

    restart_trigger_outcome = str(restart_trigger_summary.get("terminal_outcome", "")).strip()
    post_z_outcome = str(post_z_summary.get("terminal_outcome", "")).strip()

    lane_reopen_authorized = bool(post_z_summary.get("lane_specific_reopen_authorized", True))
    new_lane_or_packet_authorized_now = bool(post_z_summary.get("new_lane_or_packet_authorized_now", True))

    required_restart_trigger_outcome = str(contract.get("required_restart_trigger_outcome", "")).strip()
    required_post_phase_z_outcome = str(contract.get("required_post_phase_z_outcome", "")).strip()
    required_lane_reopen_authorized = bool(contract.get("required_lane_reopen_authorized", False))
    required_new_lane_or_packet_authorized_now = bool(
        contract.get("required_new_lane_or_packet_authorized_now", False)
    )
    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    dormancy_policy = dict(contract.get("dormancy_policy", {}))
    lane_execution_disallowed = bool(dormancy_policy.get("lane_execution_disallowed", False))
    new_packet_execution_disallowed = bool(dormancy_policy.get("new_packet_execution_disallowed", False))
    restart_front_door_required = bool(dormancy_policy.get("restart_front_door_required", False))
    taxonomy_stability_required = bool(dormancy_policy.get("taxonomy_stability_required", False))
    external_evidence_monitoring_allowed = bool(
        dormancy_policy.get("external_evidence_monitoring_allowed", False)
    )
    candidate_class_ideation_allowed = bool(dormancy_policy.get("candidate_class_ideation_allowed", False))

    policy_shape_ok = all(
        key in dormancy_policy
        for key in [
            "lane_execution_disallowed",
            "new_packet_execution_disallowed",
            "restart_front_door_required",
            "taxonomy_stability_required",
            "external_evidence_monitoring_allowed",
            "candidate_class_ideation_allowed",
        ]
    )

    summary_doc_semantics_ok = (
        "No currently governed lane is authorized to reopen." in summary_doc
        and "No currently screened future candidate is authorized for active execution." in summary_doc
    )

    preconditions_ok = (
        restart_trigger_outcome == required_restart_trigger_outcome
        and post_z_outcome == required_post_phase_z_outcome
        and lane_reopen_authorized == required_lane_reopen_authorized
        and new_lane_or_packet_authorized_now == required_new_lane_or_packet_authorized_now
        and forbid_reopen
        and policy_shape_ok
        and summary_doc_semantics_ok
    )

    policy_active = (
        lane_execution_disallowed
        and new_packet_execution_disallowed
        and restart_front_door_required
        and taxonomy_stability_required
        and external_evidence_monitoring_allowed
        and candidate_class_ideation_allowed
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "CONTROLLED_DORMANCY_PROTOCOL_EVIDENCE_INCOMPLETE")
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_CONTROLLED_DORMANCY_PROTOCOL_REPAIR"
        next_action = "REPAIR_CONTROLLED_DORMANCY_POLICY_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "CONTROLLED_DORMANCY_PROTOCOL_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_CONTROLLED_DORMANCY_PRECONDITIONS_AND_RERUN"
    elif policy_active:
        terminal_outcome = "CONTROLLED_DORMANCY_PROTOCOL_ACTIVE"
        next_action = "PRESERVE_STOP_STATE_AND_ROUTE_ANY_RESTART_REQUEST_THROUGH_RESTART_TRIGGER_CONTRACT"
    else:
        terminal_outcome = "CONTROLLED_DORMANCY_PROTOCOL_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_FULL_DORMANCY_POLICY_ACTIVATION_FLAGS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "restart_trigger_outcome_match": restart_trigger_outcome == required_restart_trigger_outcome,
            "post_phase_z_outcome_match": post_z_outcome == required_post_phase_z_outcome,
            "lane_reopen_authorized_match": lane_reopen_authorized == required_lane_reopen_authorized,
            "new_lane_or_packet_authorized_now_match": new_lane_or_packet_authorized_now
            == required_new_lane_or_packet_authorized_now,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "dormancy_policy_shape_ok": policy_shape_ok,
            "summary_doc_semantics_ok": summary_doc_semantics_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "controlled_dormancy_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "restart_trigger_outcome": restart_trigger_outcome,
                "required_restart_trigger_outcome": required_restart_trigger_outcome,
                "post_phase_z_outcome": post_z_outcome,
                "required_post_phase_z_outcome": required_post_phase_z_outcome,
                "lane_reopen_authorized": lane_reopen_authorized,
                "required_lane_reopen_authorized": required_lane_reopen_authorized,
                "new_lane_or_packet_authorized_now": new_lane_or_packet_authorized_now,
                "required_new_lane_or_packet_authorized_now": required_new_lane_or_packet_authorized_now,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "dormancy_policy": dormancy_policy,
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
            "science_post_phase_z_frontier_decision_report": _ptr(post_z_path),
            "science_frontier_stop_state_summary_doc": _ptr(summary_doc_path),
        },
        "non_claim_boundary": "Repository-local controlled dormancy protocol report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate controlled dormancy protocol report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_controlled_dormancy_protocol_20260412_v0.json",
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
        "science_controlled_dormancy_protocol_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
