from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_REPORT_20260420_v0"
DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_20260420_v0.md"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_reentry_downstream_governed_review_packet_20260420_v0.json"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _has_token(text: str, token: str) -> bool:
    pattern = re.compile(rf"(?m)^\s*(?:[-*]\s+)?`?{re.escape(token)}`?\s*$")
    return bool(pattern.search(text))


def build_report(*, packet_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet_text = _read(packet_path)

    authorization_path = REPO_ROOT / "formal/output/reports/qm_stat_reentry_explicit_downstream_governance_authorization_20260420_v0.json"
    adjudication_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_post_review_adjudication_20260420_v0.json"
    execution_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_review_execution_20260420_v0.json"
    promotion_policy_path = REPO_ROOT / "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
    canonical_boundary_path = REPO_ROOT / "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md"

    authorization = _read_json(authorization_path)
    adjudication = _read_json(adjudication_path)
    execution = _read_json(execution_path)
    promotion_policy_text = _read(promotion_policy_path)
    canonical_boundary_text = _read(canonical_boundary_path)

    authorization_summary = dict(authorization.get("summary", {}))
    adjudication_summary = dict(adjudication.get("summary", {}))
    adjudication_criteria = dict(adjudication.get("criteria", {}))
    execution_summary = dict(execution.get("summary", {}))
    execution_criteria = dict(execution.get("criteria", {}))

    packet_tokens_ok = all(
        token in packet_text
        for token in (
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_ID_v0:",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_STATUS_v0: AUTHORED_BOUNDED_v0_NONCLAIM",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_SOURCE_AUTHORIZATION_REPORT_v0: formal/output/reports/qm_stat_reentry_explicit_downstream_governance_authorization_20260420_v0.json",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_SOURCE_POST_REVIEW_ADJUDICATION_REPORT_v0: formal/output/reports/research_mode_qm_stat_reentry_post_review_adjudication_20260420_v0.json",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_SOURCE_REENTRY_REVIEW_EXECUTION_REPORT_v0: formal/output/reports/research_mode_qm_stat_reentry_review_execution_20260420_v0.json",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_TARGET_ROW_v0: ROW-SEAM-QM-STAT-001",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_TARGET_SEAM_v0: SEAM-QM-STAT",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_TARGET_PACKAGE_v0: QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_SCOPE_v0: ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_ONLY",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_OUTCOME_SET_v0: READY_OR_BLOCKED_OR_HELD_ONLY",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_NONCANONICAL_RULE_v0: NO_GOVERNED_REVIEW_EXECUTION_OR_CANONICAL_MUTATION_FROM_PACKET_AUTHORING",
            "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_NEXT_ACTION_v0: EXECUTE_ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_USING_AUTHORED_PACKET_WITHOUT_CANONICAL_MUTATION",
        )
    )

    promotion_policy_ok = all(
        _has_token(
            promotion_policy_text,
            token,
        )
        for token in (
            "PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW",
            "PROMOTION_GOVERNANCE_LANE_PROMOTION_RULE_v0: CANONICAL_ROW_AND_SEAM_STATE_CHANGE_ONLY_AFTER_GOVERNED_PROMOTION_PASS",
        )
    )
    canonical_boundary_ok = all(
        _has_token(
            canonical_boundary_text,
            token,
        )
        for token in (
            "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA",
            "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT",
        )
    )

    authorization_ok = all(
        [
            authorization_summary.get("terminal_outcome") == "QM_STAT_REENTRY_SINGLE_GOVERNED_REVIEW_PATH_AUTHORIZED_NONLIVE_v0",
            authorization_summary.get("authorization_scope_token")
            == "CONTROL_SURFACE_QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_NONLIVE",
            authorization_summary.get("target_row_id") == "ROW-SEAM-QM-STAT-001",
            authorization_summary.get("target_seam_id") == "SEAM-QM-STAT",
            authorization_summary.get("next_action")
            == "AUTHOR_ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_WITHOUT_CANONICAL_MUTATION",
            authorization_summary.get("canonical_mutation_emitted") is False,
        ]
    )

    adjudication_ok = all(
        [
            adjudication_summary.get("post_review_adjudication") == "RETAIN_AS_BOUNDED_REENTRY_REVIEWED_CANDIDATE",
            adjudication_summary.get("candidate_disposition") == "RETAIN_BOUNDED_REENTRY_REVIEWED_CANDIDATE",
            adjudication_summary.get("target_row_id") == "ROW-SEAM-QM-STAT-001",
            adjudication_summary.get("target_seam_id") == "SEAM-QM-STAT",
            adjudication_summary.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            adjudication_criteria.get("binding_preserved") is True,
            adjudication_criteria.get("governance_hold_supported") is True,
        ]
    )

    execution_ok = all(
        [
            execution_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_COMPLETED_WITH_NO_CANONICAL_ACTION",
            execution_summary.get("review_decision") == "bounded_reentry_review_completed_with_no_canonical_action",
            execution_summary.get("target_row_id") == "ROW-SEAM-QM-STAT-001",
            execution_summary.get("target_seam_id") == "SEAM-QM-STAT",
            execution_summary.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            execution_criteria.get("canonical_action_boundary_present") is True,
            execution_criteria.get("target_binding_preserved") is True,
            execution_summary.get("canonical_mutation_emitted") is False,
        ]
    )

    preconditions_ok = all([packet_tokens_ok, promotion_policy_ok, canonical_boundary_ok, authorization_ok, adjudication_ok, execution_ok])

    if not all([packet_tokens_ok, promotion_policy_ok, canonical_boundary_ok]):
        terminal_outcome = "HOLD_PENDING_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_REPAIR"
        packet_decision = "downstream_governed_review_packet_repair_required"
        next_action = "REPAIR_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_FIELDS_AND_RERUN"
    elif preconditions_ok:
        terminal_outcome = "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_READY"
        packet_decision = "downstream_governed_review_packet_ready"
        next_action = "EXECUTE_ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_USING_AUTHORED_PACKET_WITHOUT_CANONICAL_MUTATION"
    elif not authorization_ok:
        terminal_outcome = "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_BLOCKED"
        packet_decision = "downstream_governed_review_packet_blocked"
        next_action = "RESTORE_QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_BEFORE_PACKET_USE"
    else:
        terminal_outcome = "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_EVIDENCE_INCOMPLETE"
        packet_decision = "downstream_governed_review_packet_evidence_incomplete"
        next_action = "RESTORE_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_PRECONDITIONS_AND_RERUN"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_required_tokens_present": packet_tokens_ok,
            "authorization_present": authorization_ok,
            "retained_candidate_preserved": adjudication_ok,
            "review_completion_preserved": execution_ok,
            "promotion_policy_tokens_present": promotion_policy_ok,
            "canonical_boundary_tokens_present": canonical_boundary_ok,
        },
        "objective_quality": {
            "criteria": {
                "single_outcome_materialized": True,
                "canonical_mutation_withheld": True,
                "governed_review_not_yet_started": True,
                "packet_ready_or_bounded": terminal_outcome
                in {
                    "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_READY",
                    "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_BLOCKED",
                    "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_REPAIR",
                },
            },
            "inputs": {
                "authorization_terminal_outcome": authorization_summary.get("terminal_outcome"),
                "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
                "review_terminal_outcome": execution_summary.get("terminal_outcome"),
                "target_row_id": adjudication_summary.get("target_row_id"),
                "target_seam_id": adjudication_summary.get("target_seam_id"),
                "target_package_id": adjudication_summary.get("target_package_id"),
            },
            "summary": {
                "all_criteria_satisfied": preconditions_ok,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "packet_decision": packet_decision,
            "target_row_id": adjudication_summary.get("target_row_id"),
            "target_seam_id": adjudication_summary.get("target_seam_id"),
            "target_package_id": adjudication_summary.get("target_package_id"),
            "authorization_scope_token": authorization_summary.get("authorization_scope_token"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet": _ptr(packet_path),
            "authorization_report": _ptr(authorization_path),
            "post_review_adjudication_report": _ptr(adjudication_path),
            "reentry_review_execution_report": _ptr(execution_path),
            "promotion_governance_lane_policy": _ptr(promotion_policy_path),
            "canonical_action_promotion_standard": _ptr(canonical_boundary_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT downstream governed review packet report only; no governed review execution, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT downstream governed review packet report.")
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(packet_path=packet_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qm_stat_reentry_downstream_governed_review_packet_report: "
        f"decision={payload['summary']['packet_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())