from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_20260414_v0.json"
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


def _row_entry(rows: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    for row in rows:
        if str(row.get("row_id", "")).strip() == row_id:
            return dict(row)
    return {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    dossier_contract = dict(declaration.get("authorization_dossier_contract", {}))
    outcome_contract = dict(declaration.get("authorization_dossier_outcome_contract", {}))

    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()
    ledger_path = REPO_ROOT / str(required_inputs.get("physics_progress_ledger_report", "")).strip()
    p82_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_standard_formalization_report", "")
    ).strip()
    p81_path = REPO_ROOT / str(required_inputs.get("science_restart_higher_level_policy_trigger_report", "")).strip()
    p75_path = REPO_ROOT / str(required_inputs.get("science_restart_trigger_contract_report", "")).strip()
    p77_path = REPO_ROOT / str(required_inputs.get("science_dormancy_preservation_audit_report", "")).strip()

    queue = _read_json(queue_path)
    ledger = _read_json(ledger_path)
    p82 = _read_json(p82_path)
    p81 = _read_json(p81_path)
    p75 = _read_json(p75_path)
    p77 = _read_json(p77_path)

    target_row_id = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()
    target_blocker_class = str(target_seam.get("blocker_class", "")).strip()

    queue_summary = dict(queue.get("summary", {}))
    queue_entry = _row_entry(list(queue.get("ranked_candidates", [])), target_row_id)
    ledger_row_entry = _row_entry(
        list(dict(ledger.get("evidence_bundle", {})).get("closure_map", {}).get("row_level_evidence", [])),
        target_row_id,
    )

    minimum_tranche = dict(dossier_contract.get("minimum_post_authorization_tranche", {}))
    tranche_shape_ok = all(
        key in minimum_tranche
        for key in [
            "target_row_id",
            "target_lane",
            "current_status",
            "required_evidence_surface",
            "required_closure_artifact",
            "required_closure_gate",
            "required_exit_criterion",
            "bounded_scope",
        ]
    )

    top_rank_row = str(queue_summary.get("top_rank_row", "")).strip()
    progress_classification = str(ledger.get("progress_classification", "")).strip()
    required_current_restart_blocker = str(dossier_contract.get("required_current_restart_blocker", "")).strip()

    p82_summary = dict(p82.get("summary", {}))
    p82_criteria = dict(p82.get("criteria", {}))
    p81_summary = dict(p81.get("summary", {}))
    p75_summary = dict(p75.get("summary", {}))
    p77_summary = dict(p77.get("summary", {}))

    approval_blockers = list(p82_summary.get("remaining_blockers_to_authorization", []))
    policy_standard_defined = bool(p82_criteria.get("policy_standard_defined", False))
    policy_standard_approved = bool(p82_criteria.get("policy_standard_approved", False))
    higher_level_policy_revision_authorized = bool(
        p81_summary.get("higher_level_policy_revision_authorized", True)
    )
    restart_direct_execution_authorized_now = bool(p75_summary.get("direct_execution_authorized_now", True))
    dormancy_direct_execution_authorized_now = bool(p77_summary.get("direct_execution_authorized_now", True))
    restart_next_action = str(p75_summary.get("next_action", "")).strip()

    active_restart_blocker = ""
    if approval_blockers:
        active_restart_blocker = str(approval_blockers[0]).strip()
    elif restart_next_action == "DECLARE_ANTI_ALIAS_PROOF_BEFORE_OPENING_PRE_SCREENING_GATE":
        active_restart_blocker = "anti_alias_proof_for_new_candidate_not_declared"

    queue_alignment = bool(queue_entry) and all(
        [
            top_rank_row == str(dossier_contract.get("required_discovery_queue_top_rank_row", "")).strip(),
            str(queue_entry.get("row_id", "")).strip() == target_row_id,
            str(queue_entry.get("lane", "")).strip() == target_lane,
            str(queue_entry.get("blocker_class", "")).strip() == target_blocker_class,
            str(queue_entry.get("required_closure_artifact", "")).strip()
            == str(minimum_tranche.get("required_closure_artifact", "")).strip(),
            str(queue_entry.get("closure_gate", "")).strip()
            == str(minimum_tranche.get("required_closure_gate", "")).strip(),
        ]
    )
    ledger_alignment = bool(ledger_row_entry) and all(
        [
            str(ledger_row_entry.get("row_id", "")).strip() == target_row_id,
            str(ledger_row_entry.get("blocker_class", "")).strip() == target_blocker_class,
            str(ledger_row_entry.get("required_closure_artifact", "")).strip()
            == str(minimum_tranche.get("required_closure_artifact", "")).strip(),
            str(ledger_row_entry.get("closure_gate", "")).strip()
            == str(minimum_tranche.get("required_closure_gate", "")).strip(),
            str(ledger_row_entry.get("exit_criterion", "")).strip()
            == str(minimum_tranche.get("required_exit_criterion", "")).strip(),
        ]
    )

    preconditions_ok = all(
        [
            queue_alignment,
            ledger_alignment,
            tranche_shape_ok,
            progress_classification == str(dossier_contract.get("required_progress_classification", "")).strip(),
            required_current_restart_blocker == active_restart_blocker,
            policy_standard_defined == bool(dossier_contract.get("require_policy_standard_defined", False)),
            policy_standard_approved == bool(dossier_contract.get("require_policy_standard_approved", False)),
            higher_level_policy_revision_authorized
            == bool(dossier_contract.get("require_higher_level_policy_revision_authorized", False)),
            str(p75_summary.get("terminal_outcome", "")).strip()
            == str(dossier_contract.get("required_restart_terminal_outcome", "")).strip(),
            str(p77_summary.get("terminal_outcome", "")).strip()
            == str(dossier_contract.get("required_dormancy_terminal_outcome", "")).strip(),
            restart_direct_execution_authorized_now
            == bool(dossier_contract.get("required_direct_execution_authorized_now", False)),
            dormancy_direct_execution_authorized_now
            == bool(dossier_contract.get("required_direct_execution_authorized_now", False)),
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE")
    ).strip()

    if not tranche_shape_ok:
        terminal_outcome = "HOLD_PENDING_QM_STAT_SEAM_AUTHORIZATION_DOSSIER_REPAIR"
        next_action = "REPAIR_MINIMUM_POST_AUTHORIZATION_TRANCHE_SHAPE"
    elif preconditions_ok:
        if active_restart_blocker == "anti_alias_proof_for_new_candidate_not_declared":
            terminal_outcome = "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_BUT_RESTART_BLOCKED"
            next_action = "DECLARE_ANTI_ALIAS_PROOF_BEFORE_OPENING_PRE_SCREENING_GATE"
        elif active_restart_blocker:
            terminal_outcome = "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_BUT_RESTART_BLOCKED"
            next_action = "RECORD_POLICY_STANDARD_APPROVAL_BEFORE_ANY_QM_STAT_RESTART_AUTHORIZATION"
        elif str(p75_summary.get("terminal_outcome", "")).strip() == "OPEN_ONE_BOUNDED_PRE_SCREENING_RESTART_GATE":
            terminal_outcome = "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING"
            next_action = "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION"
        else:
            terminal_outcome = "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE"
            next_action = "RESTORE_QM_STAT_SEAM_AUTHORIZATION_DOSSIER_PRECONDITIONS_AND_RERUN"
    else:
        terminal_outcome = "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_SEAM_AUTHORIZATION_DOSSIER_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_row_remains_top_ranked": top_rank_row
            == str(dossier_contract.get("required_discovery_queue_top_rank_row", "")).strip(),
            "queue_alignment_ok": queue_alignment,
            "ledger_alignment_ok": ledger_alignment,
            "progress_classification_match": progress_classification
            == str(dossier_contract.get("required_progress_classification", "")).strip(),
            "current_restart_blocker_match": required_current_restart_blocker == active_restart_blocker,
            "policy_standard_defined_match": policy_standard_defined
            == bool(dossier_contract.get("require_policy_standard_defined", False)),
            "policy_standard_approved_match": policy_standard_approved
            == bool(dossier_contract.get("require_policy_standard_approved", False)),
            "higher_level_policy_revision_authorized_match": higher_level_policy_revision_authorized
            == bool(dossier_contract.get("require_higher_level_policy_revision_authorized", False)),
            "restart_terminal_outcome_match": str(p75_summary.get("terminal_outcome", "")).strip()
            == str(dossier_contract.get("required_restart_terminal_outcome", "")).strip(),
            "dormancy_terminal_outcome_match": str(p77_summary.get("terminal_outcome", "")).strip()
            == str(dossier_contract.get("required_dormancy_terminal_outcome", "")).strip(),
            "direct_execution_authorized_now_match": restart_direct_execution_authorized_now
            == bool(dossier_contract.get("required_direct_execution_authorized_now", False)),
            "minimum_post_authorization_tranche_shape_ok": tranche_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorization_dossier_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_lane": target_lane,
                "target_blocker_class": target_blocker_class,
                "discovery_queue_top_rank_row": top_rank_row,
                "progress_classification": progress_classification,
                "approval_blockers": approval_blockers,
                "required_current_restart_blocker": required_current_restart_blocker or None,
                "active_restart_blocker": active_restart_blocker or None,
                "policy_standard_defined": policy_standard_defined,
                "policy_standard_approved": policy_standard_approved,
                "higher_level_policy_revision_authorized": higher_level_policy_revision_authorized,
                "restart_terminal_outcome": p75_summary.get("terminal_outcome"),
                "restart_next_action": restart_next_action or None,
                "dormancy_terminal_outcome": p77_summary.get("terminal_outcome"),
                "direct_execution_authorized_now": restart_direct_execution_authorized_now,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "target_row_dossier": {
            "target_seam": target_seam,
            "discovery_priority_entry": queue_entry,
            "ledger_row_evidence": ledger_row_entry,
            "minimum_post_authorization_tranche": minimum_tranche,
            "current_restart_blocker": active_restart_blocker,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_lane": target_lane,
            "current_restart_blocker": active_restart_blocker,
            "current_restart_blocker_still_active": bool(active_restart_blocker),
            "first_bounded_post_authorization_artifact": minimum_tranche.get("required_closure_artifact"),
            "first_bounded_post_authorization_gate": minimum_tranche.get("required_closure_gate"),
            "next_action": next_action,
            "single_layer_only": bool(dossier_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(dossier_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_priority_queue_report": _ptr(queue_path),
            "physics_progress_ledger_report": _ptr(ledger_path),
            "bridge_external_validation_policy_standard_formalization_report": _ptr(p82_path),
            "science_restart_higher_level_policy_trigger_report": _ptr(p81_path),
            "science_restart_trigger_contract_report": _ptr(p75_path),
            "science_dormancy_preservation_audit_report": _ptr(p77_path)
        },
        "non_claim_boundary": "Repository-local QM-STAT seam authorization readiness dossier report only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT seam authorization readiness dossier report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
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
        "qm_stat_seam_authorization_readiness_dossier_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} "
        f"target_row_id={payload['summary']['target_row_id']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())