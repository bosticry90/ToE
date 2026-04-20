from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import research_mode_qm_stat_reentry_support_artifact_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_ELIGIBILITY_REVIEW_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_ELIGIBILITY_REVIEW_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_eligibility_review_20260419_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("eligibility_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    adjudication_path = REPO_ROOT / _text(required_inputs.get("post_review_adjudication_report"))
    evidence_path = REPO_ROOT / _text(required_inputs.get("live_authority_evidence_report"))
    support_artifact_path = REPO_ROOT / _text(required_inputs.get("reentry_support_artifact_report"))

    adjudication_report = _read_json(adjudication_path)
    evidence_report = _read_json(evidence_path)
    if support_artifact_path.exists():
        support_artifact_report = _read_json(support_artifact_path)
    else:
        support_artifact_report = research_mode_qm_stat_reentry_support_artifact_report.build_payload(
            declaration_path=research_mode_qm_stat_reentry_support_artifact_report.DEFAULT_DECLARATION_PATH,
            captured_at_utc=captured_at_utc,
        )

    adjudication_summary = dict(adjudication_report.get("summary", {}))
    adjudication_criteria = dict(adjudication_report.get("criteria", {}))
    evidence_summary = dict(evidence_report.get("summary", {}))
    evidence_criteria = dict(evidence_report.get("criteria", {}))
    evidence_objective_summary = dict(evidence_report.get("objective_quality", {}).get("summary", {}))
    support_summary = dict(support_artifact_report.get("summary", {}))
    support_criteria = dict(support_artifact_report.get("criteria", {}))

    retained_reviewed_candidate = all(
        [
            adjudication_summary.get("post_review_adjudication") == _text(policy.get("required_post_review_adjudication")),
            adjudication_summary.get("candidate_disposition") == _text(policy.get("required_candidate_disposition")),
            adjudication_summary.get("canonical_mutation_emitted") is False,
            adjudication_criteria.get("review_completed_without_canonical_action") is True,
        ]
    )
    evidence_materialized = all(
        [
            evidence_summary.get("terminal_outcome") == _text(policy.get("required_evidence_terminal_outcome")),
            evidence_summary.get("canonical_mutation_emitted") is False,
            evidence_criteria.get("reentry_evidence_ready") is policy.get("required_evidence_ready_flag"),
        ]
    )
    target_binding_preserved = all(
        [
            adjudication_summary.get("target_row_id") == _text(policy.get("required_target_row")),
            adjudication_summary.get("target_seam_id") == _text(policy.get("required_target_seam")),
            adjudication_summary.get("target_package_id") == _text(policy.get("required_target_package_id")),
            evidence_summary.get("target_row_id") == _text(policy.get("required_target_row")),
            evidence_summary.get("target_seam_id") == _text(policy.get("required_target_seam")),
            evidence_summary.get("target_package_id") == _text(policy.get("required_target_package_id")),
        ]
    )
    conditional_reentry_only = all(
        [
            evidence_summary.get("next_action") == _text(policy.get("required_conditional_reentry_next_action")),
            evidence_objective_summary.get("next_action") == _text(policy.get("required_conditional_reentry_next_action")),
        ]
    )
    direct_queue_authorized = all(
        [
            support_summary.get("terminal_outcome") == _text(policy.get("required_support_artifact_outcome")),
            support_summary.get("authorization_status")
            == _text(policy.get("required_support_artifact_authorization_status")),
            support_summary.get("authorized_candidate_target") == _text(policy.get("required_authorized_candidate_target")),
            support_summary.get("next_action") == _text(policy.get("next_action_on_met")),
            support_summary.get("canonical_mutation_emitted") is False,
            support_criteria.get("queue_authorization_ready") is True,
        ]
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if retained_reviewed_candidate and evidence_materialized and target_binding_preserved and direct_queue_authorized:
        terminal_outcome = "QM_STAT_REENTRY_ELIGIBILITY_MET_FOR_BOUNDED_REENTRY"
        reentry_condition_status = "MET_FOR_BOUNDED_REENTRY"
        next_action = _text(policy.get("next_action_on_met"))
    elif retained_reviewed_candidate and evidence_materialized and target_binding_preserved and conditional_reentry_only:
        terminal_outcome = "QM_STAT_REENTRY_ELIGIBILITY_PARTIALLY_MET"
        reentry_condition_status = "PARTIALLY_MET"
        next_action = _text(policy.get("next_action_on_partially_met"))
    elif retained_reviewed_candidate and target_binding_preserved:
        terminal_outcome = "QM_STAT_REENTRY_ELIGIBILITY_NOT_MET"
        reentry_condition_status = "NOT_MET"
        next_action = _text(policy.get("next_action_on_not_met"))
    else:
        terminal_outcome = "QM_STAT_REENTRY_ELIGIBILITY_EVIDENCE_INCOMPLETE"
        reentry_condition_status = "INCOMPLETE"
        next_action = _text(policy.get("next_action_on_incomplete"))

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))
        reentry_condition_status = "INCOMPLETE"
        next_action = _text(policy.get("next_action_on_incomplete"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "retained_reviewed_candidate_present": retained_reviewed_candidate,
            "stronger_live_authority_evidence_materialized": evidence_materialized,
            "target_binding_preserved": target_binding_preserved,
            "reentry_still_conditional": conditional_reentry_only,
            "direct_reentry_queue_authorized": direct_queue_authorized,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_RESEARCH_MODE_QM_STAT_REENTRY_ELIGIBILITY_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule"))
            == "ONE_RESEARCH_MODE_QM_STAT_REENTRY_ELIGIBILITY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "partial_route_requires_conditional_reentry_only": (
                    terminal_outcome != "QM_STAT_REENTRY_ELIGIBILITY_PARTIALLY_MET"
                )
                or conditional_reentry_only,
                "met_route_requires_direct_queue_authorization": (
                    terminal_outcome != "QM_STAT_REENTRY_ELIGIBILITY_MET_FOR_BOUNDED_REENTRY"
                )
                or direct_queue_authorized,
                "noncanonical_boundary_preserved": True,
            },
            "inputs": {
                "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
                "candidate_disposition": adjudication_summary.get("candidate_disposition"),
                "evidence_terminal_outcome": evidence_summary.get("terminal_outcome"),
                "evidence_next_action": evidence_summary.get("next_action"),
                "support_artifact_outcome": support_summary.get("terminal_outcome"),
                "support_artifact_authorization_status": support_summary.get("authorization_status"),
                "target_row_id": evidence_summary.get("target_row_id"),
                "target_seam_id": evidence_summary.get("target_seam_id"),
                "target_package_id": evidence_summary.get("target_package_id"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE" if terminal_outcome in allowed_outcomes else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "reentry_condition_status": reentry_condition_status,
            "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
            "candidate_disposition": adjudication_summary.get("candidate_disposition"),
            "target_row_id": evidence_summary.get("target_row_id"),
            "target_seam_id": evidence_summary.get("target_seam_id"),
            "target_package_id": evidence_summary.get("target_package_id"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_review_adjudication_report": _ptr(adjudication_path),
            "live_authority_evidence_report": _ptr(evidence_path),
            "reentry_support_artifact_report": _ptr(support_artifact_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry eligibility review only; no canonical promotion, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry eligibility review report.")
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
        "research_mode_qm_stat_reentry_eligibility_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())