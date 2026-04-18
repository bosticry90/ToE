from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_20260418_v0.json"
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


def _extract_token(text: str, token: str) -> str:
    pattern = re.compile(rf"(?m)^\s*(?:[-*]\s+)?`?{re.escape(token)}`?\s*:\s*`?(\S+?)`?\s*$")
    match = pattern.search(text)
    if not match:
        raise ValueError(f"Missing token: {token}")
    return match.group(1).strip()


def _row_entry(rows: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    for row in rows:
        if str(row.get("row_id", "")).strip() == row_id:
            return dict(row)
    return {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_contract = dict(declaration.get("authorization_activation_contract", {}))
    outcome_contract = dict(declaration.get("authorization_activation_outcome_contract", {}))

    tgc93_path = REPO_ROOT / str(required_inputs.get("tgc93_branch_decision_package", "")).strip()
    sla_path = REPO_ROOT / str(required_inputs.get("seam_resolution_sla_ledger_report", "")).strip()
    transition_path = REPO_ROOT / str(required_inputs.get("discovery_queue_transition_decision_report", "")).strip()
    rescoring_path = REPO_ROOT / str(required_inputs.get("discovery_queue_rescoring_pass_report", "")).strip()
    checkpoint_path = REPO_ROOT / str(required_inputs.get("discovery_engine_review_checkpoint_report", "")).strip()
    scoring_review_path = REPO_ROOT / str(required_inputs.get("discovery_engine_scoring_routing_review_report", "")).strip()

    tgc93_text = _read(tgc93_path)
    sla = _read_json(sla_path)
    transition = _read_json(transition_path)
    rescoring = _read_json(rescoring_path)
    checkpoint = _read_json(checkpoint_path)
    scoring_review = _read_json(scoring_review_path)

    target_row_id = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()
    target_blocker_class = str(target_seam.get("blocker_class", "")).strip()

    tgc93_branch_decision = _extract_token(tgc93_text, "TGC93_BRANCH_DECISION_v0")
    tgc93_reentry_authorization = _extract_token(tgc93_text, "TGC93_SEAM_REENTRY_AUTHORIZATION_v0")

    sla_entry = _row_entry(list(sla.get("entries", [])), target_row_id)
    transition_summary = dict(transition.get("summary", {}))
    rescoring_summary = dict(rescoring.get("summary", {}))
    checkpoint_summary = dict(checkpoint.get("summary", {}))
    scoring_summary = dict(scoring_review.get("summary", {}))

    minimum_tranche = dict(decision_contract.get("minimum_bounded_activation_tranche", {}))
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

    candidate_selection_ok = all(
        [
            tgc93_branch_decision == str(decision_contract.get("required_tgc93_branch_decision", "")).strip(),
            tgc93_reentry_authorization
            == str(decision_contract.get("required_tgc93_seam_reentry_authorization", "")).strip(),
            str(transition_summary.get("next_ranked_row_id", "")).strip()
            == str(decision_contract.get("required_transition_next_ranked_row", "")).strip(),
            str(transition_summary.get("next_ranked_lane", "")).strip()
            == str(decision_contract.get("required_transition_next_ranked_lane", "")).strip(),
            int(transition_summary.get("max_new_seam_activations_per_cycle", 0))
            == int(decision_contract.get("required_single_activation_cap", 0)),
            str(rescoring_summary.get("rank3_candidate", "")).strip()
            == str(decision_contract.get("required_rescoring_rank3_candidate", "")).strip(),
            str(rescoring_summary.get("terminal_route", "")).strip()
            == str(decision_contract.get("required_rescoring_terminal_route", "")).strip(),
            str(sla_entry.get("decision_state", "")).strip()
            == str(decision_contract.get("required_sla_decision_state", "")).strip(),
            str(sla_entry.get("gate_runtime_status", "")).strip()
            == str(decision_contract.get("required_sla_gate_runtime_status", "")).strip(),
            str(sla_entry.get("lane", "")).strip() == target_lane,
            str(sla_entry.get("blocker_class", "")).strip() == target_blocker_class,
            str(sla_entry.get("target_surface", "")).strip()
            == str(minimum_tranche.get("required_evidence_surface", "")).strip(),
            str(sla_entry.get("artifact_surface", "")).strip()
            == str(minimum_tranche.get("required_closure_artifact", "")).strip(),
            str(sla_entry.get("gate_surface", "")).strip()
            == str(minimum_tranche.get("required_closure_gate", "")).strip(),
            str(sla_entry.get("exit_criterion", "")).strip()
            == str(minimum_tranche.get("required_exit_criterion", "")).strip(),
            str(scoring_summary.get("lane_expansion_reopen_condition", "")).strip()
            == str(decision_contract.get("required_lane_expansion_reopen_condition", "")).strip(),
        ]
    )

    hold_path_active = all(
        [
            str(checkpoint_summary.get("selected_expansion_decision", "")).strip()
            == str(decision_contract.get("hold_selected_expansion_decision", "")).strip(),
            str(scoring_summary.get("selected_review_disposition", "")).strip()
            == str(decision_contract.get("hold_review_disposition", "")).strip(),
            bool(scoring_summary.get("credible_external_path_signal_present", True))
            is False,
        ]
    )

    activation_now_authorized = all(
        [
            str(checkpoint_summary.get("selected_expansion_decision", "")).strip()
            == str(decision_contract.get("authorized_selected_expansion_decision", "")).strip(),
            bool(scoring_summary.get("credible_external_path_signal_present", False))
            == bool(decision_contract.get("authorized_external_path_signal_present", False)),
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "COSMO_SR_AUTHORIZATION_ACTIVATION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not tranche_shape_ok:
        terminal_outcome = "HOLD_PENDING_COSMO_SR_AUTHORIZATION_ACTIVATION_REPAIR"
        next_action = "REPAIR_MINIMUM_BOUNDED_ACTIVATION_TRANCHE_SHAPE"
    elif candidate_selection_ok and hold_path_active:
        terminal_outcome = "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD"
        next_action = "RESOLVE_DISCOVERY_REVIEW_HOLD_ONCE_BEFORE_ANY_COSMO_SR_ACTIVATION"
    elif candidate_selection_ok and activation_now_authorized:
        terminal_outcome = "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_AUTHORIZED"
        next_action = "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_SEAM_ACTIVATION_ONLY"
    else:
        terminal_outcome = "COSMO_SR_AUTHORIZATION_ACTIVATION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_COSMO_SR_AUTHORIZATION_ACTIVATION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "tgc93_branch_authorizes_single_seam_reentry": tgc93_branch_decision
            == str(decision_contract.get("required_tgc93_branch_decision", "")).strip(),
            "tgc93_reentry_authorization_is_active": tgc93_reentry_authorization
            == str(decision_contract.get("required_tgc93_seam_reentry_authorization", "")).strip(),
            "candidate_selection_ok": candidate_selection_ok,
            "minimum_bounded_activation_tranche_shape_ok": tranche_shape_ok,
            "hold_path_active": hold_path_active,
            "activation_now_authorized": activation_now_authorized,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "single_non_frozen_candidate_confirmed": candidate_selection_ok,
                "bounded_activation_surface_materialized": tranche_shape_ok,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_lane": target_lane,
                "tgc93_branch_decision": tgc93_branch_decision,
                "tgc93_seam_reentry_authorization": tgc93_reentry_authorization,
                "transition_selected_route": transition_summary.get("selected_route"),
                "transition_next_ranked_row_id": transition_summary.get("next_ranked_row_id"),
                "rescoring_terminal_route": rescoring_summary.get("terminal_route"),
                "checkpoint_selected_expansion_decision": checkpoint_summary.get("selected_expansion_decision"),
                "scoring_review_disposition": scoring_summary.get("selected_review_disposition"),
                "credible_external_path_signal_present": scoring_summary.get("credible_external_path_signal_present"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "target_row_decision": {
            "target_seam": target_seam,
            "seam_resolution_entry": sla_entry,
            "minimum_bounded_activation_tranche": minimum_tranche,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_lane": target_lane,
            "single_non_frozen_candidate_confirmed": candidate_selection_ok,
            "activation_authorized_now": terminal_outcome == "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_AUTHORIZED",
            "activation_hold_reason": checkpoint_summary.get("selected_expansion_decision")
            if terminal_outcome == "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD"
            else "",
            "first_bounded_activation_artifact": minimum_tranche.get("required_closure_artifact"),
            "first_bounded_activation_gate": minimum_tranche.get("required_closure_gate"),
            "next_action": next_action,
            "single_layer_only": bool(decision_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(decision_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "tgc93_branch_decision_package": _ptr(tgc93_path),
            "seam_resolution_sla_ledger_report": _ptr(sla_path),
            "discovery_queue_transition_decision_report": _ptr(transition_path),
            "discovery_queue_rescoring_pass_report": _ptr(rescoring_path),
            "discovery_engine_review_checkpoint_report": _ptr(checkpoint_path),
            "discovery_engine_scoring_routing_review_report": _ptr(scoring_review_path),
        },
        "non_claim_boundary": "Repository-local COSMO-SR seam authorization and activation decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the COSMO-SR seam authorization and activation decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "cosmo_sr_seam_authorization_activation_decision_20260418_v0.json",
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
        "cosmo_sr_seam_authorization_activation_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())