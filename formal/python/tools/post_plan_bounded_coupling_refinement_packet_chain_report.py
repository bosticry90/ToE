from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json"
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
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    authority_review_path = REPO_ROOT / str(required_inputs.get("post_plan_authority_coupling_review_path_report", "")).strip()
    packet_path = REPO_ROOT / str(required_inputs.get("bounded_coupling_refinement_packet_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("coupling_refinement_ruling_report", "")).strip()
    registration_path = REPO_ROOT / str(required_inputs.get("authority_promotion_registration_report", "")).strip()

    authority_review_report = _read_json(authority_review_path)
    packet_report = _read_json(packet_path)
    ruling_report = _read_json(ruling_path)
    registration_report = _read_json(registration_path)

    authority_review_ok = (
        authority_review_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_authority_review_path_outcome", "")).strip()
        and authority_review_report.get("summary", {}).get("next_action") == str(policy.get("required_authority_review_path_next_action", "")).strip()
    )

    packet_summary = dict(packet_report.get("summary", {}))
    ruling_summary = dict(ruling_report.get("summary", {}))
    ruling_details = dict(ruling_report.get("ruling", {}))
    registration_summary = dict(registration_report.get("summary", {}))

    execution_classification = packet_summary.get("execution_classification")
    packet_next_action = packet_summary.get("next_action")
    packet_ok = (
        execution_classification == str(policy.get("required_execution_classification", "")).strip()
        and packet_next_action == str(policy.get("required_packet_next_action", "")).strip()
    )
    ruling_id = ruling_summary.get("ruling_id") or ruling_details.get("ruling_id")
    ruling_next_action = ruling_summary.get("next_action") or ruling_details.get("next_action")
    ruling_ok = (
        ruling_id == str(policy.get("required_ruling_id", "")).strip()
        and ruling_next_action == str(policy.get("required_ruling_next_action", "")).strip()
    )
    registration_completed = registration_summary.get("registration_completed")
    authoritative = registration_summary.get("revised_definition_is_now_authoritative")
    registration_next_action = registration_summary.get("next_action")
    registration_ok = (
        registration_completed is bool(policy.get("required_registration_completed", True))
        and authoritative is bool(policy.get("required_registration_authoritative", True))
        and registration_next_action == str(policy.get("required_registration_next_action", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_EVIDENCE_INCOMPLETE")
    ).strip()

    if not authority_review_report or not packet_report or not ruling_report or not registration_report:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_REPAIR"
        next_action = "RESTORE_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_INPUTS_AND_RERUN"
    elif authority_review_ok and packet_ok and ruling_ok and registration_ok:
        terminal_outcome = "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED"
        next_action = registration_next_action
    elif authority_review_ok and packet_ok and ruling_id == "COUPLING_REFINEMENT_VALID_BUT_STILL_NONAUTHORITATIVE":
        terminal_outcome = "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_VALID_BUT_NONAUTHORITATIVE"
        next_action = ruling_next_action
    elif authority_review_ok and ruling_id == "COUPLING_REFINEMENT_NOT_FIT_FOR_AUTHORITY_USE":
        terminal_outcome = "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_NOT_FIT_FOR_AUTHORITY_USE"
        next_action = ruling_next_action
    elif authority_review_ok:
        terminal_outcome = "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_BLOCKED"
        next_action = "REPAIR_COUPLING_REFINEMENT_CHAIN_OR_HOLD_PROGRAM_STATE"
    else:
        terminal_outcome = "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "authority_review_path_materialized": authority_review_ok,
            "packet_report_materialized": packet_ok,
            "ruling_report_materialized": bool(ruling_id),
            "promotion_follow_through_materialized": bool(registration_completed),
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "packet_chain_only_opens_after_authority_review_path": (terminal_outcome != "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED") or authority_review_ok,
                "promotion_registration_only_after_promotion_ruling": (registration_next_action != "MONITOR_RECOMPUTE_SURFACES") or ruling_ok,
            },
            "inputs": {
                "authority_review_path_outcome": authority_review_report.get("summary", {}).get("terminal_outcome"),
                "authority_review_next_action": authority_review_report.get("summary", {}).get("next_action"),
                "execution_classification": execution_classification,
                "coupling_state": packet_summary.get("coupling_state"),
                "ruling_id": ruling_id,
                "ruling_classification": ruling_summary.get("classification") or ruling_details.get("classification"),
                "registration_completed": registration_completed,
                "revised_definition_is_now_authoritative": authoritative,
                "recompute_surfaces_triggered": registration_summary.get("recompute_surfaces_triggered"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": packet_summary.get("target_row_id"),
            "execution_classification": execution_classification,
            "coupling_state": packet_summary.get("coupling_state"),
            "ruling_id": ruling_id,
            "registration_completed": registration_completed,
            "revised_definition_is_now_authoritative": authoritative,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_authority_coupling_review_path_report": _ptr(authority_review_path),
            "bounded_coupling_refinement_packet_report": _ptr(packet_path),
            "coupling_refinement_ruling_report": _ptr(ruling_path),
            "authority_promotion_registration_report": _ptr(registration_path)
        },
        "non_claim_boundary": "Repository-local post-plan bounded coupling-refinement packet chain only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan bounded coupling-refinement packet chain report.")
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
        "post_plan_bounded_coupling_refinement_packet_chain_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())