from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_20260419_v0.json"
)
DEFAULT_QUEUE_OBJECT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "queue"
    / "qm_stat_reentry_review_cycle_queue_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_review_cycle_queue_20260419_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _text(value: Any) -> str:
    return str(value).strip() if value is not None else ""


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_payload(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    queue_contract = dict(declaration.get("queue_contract", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    eligibility_path = REPO_ROOT / _text(required_inputs.get("reentry_eligibility_review_report"))
    support_path = REPO_ROOT / _text(required_inputs.get("reentry_support_artifact_report"))

    eligibility_report = _read_json(eligibility_path)
    support_report = _read_json(support_path)

    eligibility_summary = dict(eligibility_report.get("summary", {}))
    eligibility_criteria = dict(eligibility_report.get("criteria", {}))
    support_summary = dict(support_report.get("summary", {}))
    support_criteria = dict(support_report.get("criteria", {}))

    queue_contract_present = all(
        _text(queue_contract.get(key))
        for key in [
            "required_eligibility_outcome",
            "required_reentry_condition_status",
            "required_eligibility_next_action",
            "required_support_artifact_outcome",
            "required_support_authorization_status",
            "required_authorized_candidate_target",
            "required_target_row",
            "required_target_seam",
            "required_target_package_id",
            "queue_scope_token",
            "queue_status_on_ready",
            "queue_packet_status_on_ready",
            "next_action_on_ready",
        ]
    )
    eligibility_ready = all(
        [
            eligibility_summary.get("terminal_outcome") == _text(queue_contract.get("required_eligibility_outcome")),
            eligibility_summary.get("reentry_condition_status")
            == _text(queue_contract.get("required_reentry_condition_status")),
            eligibility_summary.get("next_action") == _text(queue_contract.get("required_eligibility_next_action")),
            eligibility_summary.get("canonical_mutation_emitted") is False,
            eligibility_criteria.get("direct_reentry_queue_authorized") is True,
        ]
    )
    support_ready = all(
        [
            support_summary.get("terminal_outcome") == _text(queue_contract.get("required_support_artifact_outcome")),
            support_summary.get("authorization_status")
            == _text(queue_contract.get("required_support_authorization_status")),
            support_summary.get("authorized_candidate_target")
            == _text(queue_contract.get("required_authorized_candidate_target")),
            support_summary.get("canonical_mutation_emitted") is False,
            support_criteria.get("queue_authorization_ready") is True,
        ]
    )
    target_binding_preserved = all(
        [
            eligibility_summary.get("target_row_id") == _text(queue_contract.get("required_target_row")),
            eligibility_summary.get("target_seam_id") == _text(queue_contract.get("required_target_seam")),
            eligibility_summary.get("target_package_id") == _text(queue_contract.get("required_target_package_id")),
            support_summary.get("target_row_id") == _text(queue_contract.get("required_target_row")),
            support_summary.get("target_seam_id") == _text(queue_contract.get("required_target_seam")),
            support_summary.get("target_package_id") == _text(queue_contract.get("required_target_package_id")),
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    if not queue_contract_present:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_BLOCKED_BY_MISSING_QUEUE_CONTRACT"
        next_action = _text(queue_contract.get("next_action_on_blocked"))
    elif eligibility_ready and support_ready and target_binding_preserved:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
        next_action = _text(queue_contract.get("next_action_on_ready"))
    elif eligibility_ready and support_ready:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_HELD_PENDING_QUEUE_PACKET"
        next_action = _text(queue_contract.get("next_action_on_hold"))
    else:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_EVIDENCE_INCOMPLETE"
        next_action = _text(queue_contract.get("next_action_on_blocked"))

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(outcome_contract.get("default_outcome"))

    queue_object = {
        "queue_id": "qm_stat_reentry_review_cycle_queue_20260419_v0",
        "queue_class": "BOUNDED_REENTRY_REVIEW_CYCLE_QUEUE",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "queue_status": _text(queue_contract.get("queue_status_on_ready"))
        if terminal_outcome == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
        else "NOT_QUEUED",
        "queue_scope_token": _text(queue_contract.get("queue_scope_token")),
        "queue_packet_status": _text(queue_contract.get("queue_packet_status_on_ready"))
        if terminal_outcome == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
        else "NO_QUEUE_PACKET",
        "authorized_candidate_target": _text(queue_contract.get("required_authorized_candidate_target")),
        "target_binding": {
            "row_id": _text(queue_contract.get("required_target_row")),
            "seam_id": _text(queue_contract.get("required_target_seam")),
            "target_package_id": _text(queue_contract.get("required_target_package_id")),
        },
        "source_bundle": {
            "reentry_eligibility_review_report": _ptr(eligibility_path),
            "reentry_support_artifact_report": _ptr(support_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry review-cycle queue only; no canonical promotion, canonical mutation, or seam-closure claim.",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": queue_object["captured_at_utc"],
        "criteria": {
            "queue_contract_present": queue_contract_present,
            "eligibility_ready_for_queue": eligibility_ready,
            "support_artifact_ready_for_queue": support_ready,
            "target_binding_preserved": target_binding_preserved,
            "single_terminal_outcome_rule_declared": _text(outcome_contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_OUTCOME",
            "no_loop_rule_declared": _text(outcome_contract.get("no_loop_rule"))
            == "ONE_RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "queue_placement_requires_explicit_authorization": (
                    terminal_outcome != "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
                )
                or (eligibility_ready and support_ready),
                "noncanonical_boundary_preserved": True,
            },
            "inputs": {
                "eligibility_terminal_outcome": eligibility_summary.get("terminal_outcome"),
                "eligibility_next_action": eligibility_summary.get("next_action"),
                "support_artifact_outcome": support_summary.get("terminal_outcome"),
                "support_authorization_status": support_summary.get("authorization_status"),
                "authorized_candidate_target": _text(queue_contract.get("required_authorized_candidate_target")),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE" if terminal_outcome in allowed_outcomes else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "queue_status": queue_object["queue_status"],
            "queue_packet_status": queue_object["queue_packet_status"],
            "authorized_candidate_target": _text(queue_contract.get("required_authorized_candidate_target")),
            "target_row_id": _text(queue_contract.get("required_target_row")),
            "target_seam_id": _text(queue_contract.get("required_target_seam")),
            "target_package_id": _text(queue_contract.get("required_target_package_id")),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "queue_object": queue_object,
        "source_bundle": queue_object["source_bundle"],
        "non_claim_boundary": queue_object["non_claim_boundary"],
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry review-cycle queue report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--queue-out", type=Path, default=DEFAULT_QUEUE_OBJECT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    queue_out = ns.queue_out if ns.queue_out.is_absolute() else (REPO_ROOT / ns.queue_out)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_payload(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    queue_out.parent.mkdir(parents=True, exist_ok=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    queue_out.write_text(json.dumps(payload["queue_object"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "research_mode_qm_stat_reentry_review_cycle_queue_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())