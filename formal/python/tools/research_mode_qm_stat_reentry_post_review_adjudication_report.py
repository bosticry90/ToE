from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_POST_REVIEW_ADJUDICATION_REPORT_20260420_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_POST_REVIEW_ADJUDICATION_20260420_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_post_review_adjudication_20260420_v0.json"
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
    adjudication_policy = dict(declaration.get("adjudication_policy", {}))
    candidate_routes = list(declaration.get("candidate_routes", []))

    review_report_path = REPO_ROOT / str(required_inputs.get("review_execution_report", "")).strip()
    packet_report_path = REPO_ROOT / str(required_inputs.get("review_packet_report", "")).strip()
    intake_report_path = REPO_ROOT / str(required_inputs.get("intake_decision_report", "")).strip()
    queue_packet_report_path = REPO_ROOT / str(required_inputs.get("queue_packet_report", "")).strip()
    queue_report_path = REPO_ROOT / str(required_inputs.get("queue_report", "")).strip()

    review_report = _read_json(review_report_path)
    packet_report = _read_json(packet_report_path)
    intake_report = _read_json(intake_report_path)
    queue_packet_report = _read_json(queue_packet_report_path)
    queue_report = _read_json(queue_report_path)

    review_summary = dict(review_report.get("summary", {}))
    review_criteria = dict(review_report.get("criteria", {}))
    review_objective_summary = dict(review_report.get("objective_quality", {}).get("summary", {}))
    packet_summary = dict(packet_report.get("summary", {}))
    intake_summary = dict(intake_report.get("summary", {}))
    queue_packet_summary = dict(queue_packet_report.get("summary", {}))
    queue_report_summary = dict(queue_report.get("summary", {}))

    reviewed_without_canonical_action = (
        review_summary.get("terminal_outcome") == str(adjudication_policy.get("required_review_terminal_outcome", "")).strip()
        and review_summary.get("review_decision") == str(adjudication_policy.get("required_review_decision", "")).strip()
        and review_summary.get("canonical_mutation_emitted") is False
    )
    execution_chain_preserved = (
        review_criteria.get("packet_ready") is True
        and review_criteria.get("intake_acceptance_present") is True
        and review_criteria.get("queue_anchor_preserved") is True
        and packet_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_READY"
        and intake_summary.get("terminal_outcome") == "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_ACCEPTED_FOR_BOUNDED_EXECUTION_PACKET_AUTHORING"
        and queue_packet_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF"
        and queue_report_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
    )
    binding_preserved = (
        review_summary.get("target_row_id") == str(adjudication_policy.get("required_target_row", "")).strip()
        and review_summary.get("target_seam_id") == str(adjudication_policy.get("required_target_seam", "")).strip()
        and review_summary.get("target_package_id") == str(adjudication_policy.get("required_target_package_id", "")).strip()
        and packet_summary.get("target_row_id") == review_summary.get("target_row_id")
        and packet_summary.get("target_seam_id") == review_summary.get("target_seam_id")
        and packet_summary.get("target_package_id") == review_summary.get("target_package_id")
        and intake_summary.get("target_row_id") == review_summary.get("target_row_id")
        and queue_packet_summary.get("target_row_id") == review_summary.get("target_row_id")
        and queue_report_summary.get("target_row_id") == review_summary.get("target_row_id")
    )
    governance_hold_supported = (
        reviewed_without_canonical_action
        and execution_chain_preserved
        and binding_preserved
        and review_objective_summary.get("next_action")
        == str(adjudication_policy.get("required_prior_next_action", "")).strip()
    )

    if reviewed_without_canonical_action and execution_chain_preserved and binding_preserved:
        decision = "RETAIN_AS_BOUNDED_REENTRY_REVIEWED_CANDIDATE"
        disposition = "RETAIN_BOUNDED_REENTRY_REVIEWED_CANDIDATE"
        next_action = str(adjudication_policy.get("required_next_action_on_retain", "")).strip()
    elif reviewed_without_canonical_action and binding_preserved and not execution_chain_preserved:
        decision = "HOLD_PENDING_ADDITIONAL_REENTRY_SUPPORT"
        disposition = "HOLD_FOR_ADDITIONAL_REENTRY_SUPPORT"
        next_action = str(adjudication_policy.get("required_next_action_on_hold", "")).strip()
    elif not binding_preserved:
        decision = "PRUNE_ACTIVE_REENTRY_ROUTE"
        disposition = "PRUNE_ACTIVE_REENTRY_ROUTE"
        next_action = str(adjudication_policy.get("required_next_action_on_prune", "")).strip()
    elif governance_hold_supported:
        decision = "EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_REQUIRED"
        disposition = "GOVERNANCE_AUTHORIZATION_REQUIRED"
        next_action = str(adjudication_policy.get("required_next_action_on_governance_hold", "")).strip()
    else:
        decision = "REENTRY_POST_REVIEW_ADJUDICATION_EVIDENCE_INCOMPLETE"
        disposition = "EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_REENTRY_POST_REVIEW_ADJUDICATION_INPUTS_AND_RERUN"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "review_completed_without_canonical_action": reviewed_without_canonical_action,
            "execution_chain_preserved": execution_chain_preserved,
            "binding_preserved": binding_preserved,
            "governance_hold_supported": governance_hold_supported,
            "bounded_decision_materialized": decision != "REENTRY_POST_REVIEW_ADJUDICATION_EVIDENCE_INCOMPLETE",
        },
        "objective_quality": {
            "criteria": {
                "retain_route_assessed": True,
                "hold_route_assessed": True,
                "prune_route_assessed": True,
                "governance_hold_route_assessed": True,
                "decision_materialized": decision != "REENTRY_POST_REVIEW_ADJUDICATION_EVIDENCE_INCOMPLETE",
            },
            "inputs": {
                "review_terminal_outcome": review_summary.get("terminal_outcome"),
                "review_decision": review_summary.get("review_decision"),
                "target_row_id": review_summary.get("target_row_id"),
                "target_seam_id": review_summary.get("target_seam_id"),
                "target_package_id": review_summary.get("target_package_id"),
                "authorized_candidate_target": review_summary.get("authorized_candidate_target"),
                "candidate_routes": candidate_routes,
            },
            "summary": {
                "all_criteria_satisfied": decision != "REENTRY_POST_REVIEW_ADJUDICATION_EVIDENCE_INCOMPLETE",
                "phase_status": "COMPLETE" if decision != "REENTRY_POST_REVIEW_ADJUDICATION_EVIDENCE_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "post_review_adjudication": decision,
            "candidate_disposition": disposition,
            "review_terminal_outcome": review_summary.get("terminal_outcome"),
            "review_decision": review_summary.get("review_decision"),
            "target_row_id": review_summary.get("target_row_id"),
            "target_seam_id": review_summary.get("target_seam_id"),
            "target_package_id": review_summary.get("target_package_id"),
            "authorized_candidate_target": review_summary.get("authorized_candidate_target"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "review_execution_report": _ptr(review_report_path),
            "review_packet_report": _ptr(packet_report_path),
            "intake_decision_report": _ptr(intake_report_path),
            "queue_packet_report": _ptr(queue_packet_report_path),
            "queue_report": _ptr(queue_report_path),
        },
        "non_claim_boundary": "Repository-local re-entry post-review adjudication only; no canonical promotion, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry post-review adjudication report.")
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
        "research_mode_qm_stat_reentry_post_review_adjudication_report: "
        f"decision={payload['summary']['post_review_adjudication']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())