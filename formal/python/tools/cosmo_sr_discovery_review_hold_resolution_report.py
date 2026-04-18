from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_20260418_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    resolution_contract = dict(declaration.get("hold_resolution_contract", {}))
    outcome_contract = dict(declaration.get("hold_resolution_outcome_contract", {}))

    tgc93_path = REPO_ROOT / str(required_inputs.get("tgc93_branch_decision_package", "")).strip()
    phase2_decision_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_seam_authorization_activation_decision_report", "")).strip()
    transition_path = REPO_ROOT / str(required_inputs.get("discovery_queue_transition_decision_report", "")).strip()
    checkpoint_path = REPO_ROOT / str(required_inputs.get("discovery_engine_review_checkpoint_report", "")).strip()
    scoring_review_path = REPO_ROOT / str(required_inputs.get("discovery_engine_scoring_routing_review_report", "")).strip()

    tgc93_text = _read(tgc93_path)
    phase2_decision = _read_json(phase2_decision_path)
    transition = _read_json(transition_path)
    checkpoint = _read_json(checkpoint_path)
    scoring_review = _read_json(scoring_review_path)

    tgc93_branch_decision = _extract_token(tgc93_text, "TGC93_BRANCH_DECISION_v0")
    tgc93_seam_reentry_authorization = _extract_token(tgc93_text, "TGC93_SEAM_REENTRY_AUTHORIZATION_v0")
    phase2_summary = dict(phase2_decision.get("summary", {}))
    transition_summary = dict(transition.get("summary", {}))
    checkpoint_summary = dict(checkpoint.get("summary", {}))
    scoring_summary = dict(scoring_review.get("summary", {}))

    target_row_id = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()

    required_hold_scope_rule = str(resolution_contract.get("hold_scope_rule", "")).strip()
    hold_rule_applies_to_further_expansion = required_hold_scope_rule in str(checkpoint_summary.get("hold_policy", "")).strip()
    single_candidate_alignment = all(
        [
            str(phase2_summary.get("terminal_outcome", "")).strip()
            == str(resolution_contract.get("required_phase2_decision_outcome", "")).strip(),
            bool(phase2_summary.get("single_non_frozen_candidate_confirmed", False)),
            str(phase2_summary.get("target_row_id", "")).strip() == target_row_id,
            str(phase2_summary.get("target_lane", "")).strip() == target_lane,
            str(transition_summary.get("next_ranked_row_id", "")).strip()
            == str(resolution_contract.get("required_transition_next_ranked_row", "")).strip(),
            str(transition_summary.get("next_ranked_lane", "")).strip()
            == str(resolution_contract.get("required_transition_next_ranked_lane", "")).strip(),
            int(transition_summary.get("max_new_seam_activations_per_cycle", 0))
            == int(resolution_contract.get("required_single_activation_cap", 0)),
        ]
    )
    current_hold_state_matches = all(
        [
            str(checkpoint_summary.get("selected_expansion_decision", "")).strip()
            == str(resolution_contract.get("required_checkpoint_hold_decision", "")).strip(),
            str(scoring_summary.get("selected_review_disposition", "")).strip()
            == str(resolution_contract.get("required_scoring_review_disposition", "")).strip(),
            bool(scoring_summary.get("credible_external_path_signal_present", True))
            == bool(resolution_contract.get("required_credible_external_path_signal_present", False)),
        ]
    )
    tgc93_scope_matches = all(
        [
            tgc93_branch_decision == str(resolution_contract.get("required_tgc93_branch_decision", "")).strip(),
            tgc93_seam_reentry_authorization
            == str(resolution_contract.get("required_tgc93_seam_reentry_authorization", "")).strip(),
        ]
    )

    hold_is_scope_local_not_candidate_disqualifying = all(
        [
            hold_rule_applies_to_further_expansion,
            single_candidate_alignment,
            current_hold_state_matches,
            tgc93_scope_matches,
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not resolution_contract:
        terminal_outcome = "HOLD_PENDING_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_REPAIR"
        next_action = "REPAIR_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_DECLARATION"
    elif hold_is_scope_local_not_candidate_disqualifying:
        terminal_outcome = "COSMO_SR_SINGLE_CANDIDATE_HOLD_RESOLVED_FOR_AUTHORIZATION_CONVERSION"
        next_action = "CONVERT_HELD_COSMO_SR_PHASE2_DECISION_TO_BOUNDED_ACTIVATION_AUTHORIZATION_ONCE"
    elif current_hold_state_matches and single_candidate_alignment:
        terminal_outcome = "COSMO_SR_DISCOVERY_REVIEW_HOLD_REMAINS_ACTIVE"
        next_action = "MAINTAIN_HOLD_UNTIL_SCOPE_AND_SELECTION_CONDITIONS_ARE_REPAIRED"
    else:
        terminal_outcome = "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "tgc93_scope_matches": tgc93_scope_matches,
            "single_candidate_alignment": single_candidate_alignment,
            "current_hold_state_matches": current_hold_state_matches,
            "hold_rule_applies_to_further_expansion": hold_rule_applies_to_further_expansion,
            "hold_is_scope_local_not_candidate_disqualifying": hold_is_scope_local_not_candidate_disqualifying,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "scope_local_hold_interpretation_materialized": hold_rule_applies_to_further_expansion,
                "phase2_candidate_preserved": single_candidate_alignment,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_lane": target_lane,
                "tgc93_branch_decision": tgc93_branch_decision,
                "tgc93_seam_reentry_authorization": tgc93_seam_reentry_authorization,
                "phase2_terminal_outcome": phase2_summary.get("terminal_outcome"),
                "checkpoint_hold_policy": checkpoint_summary.get("hold_policy"),
                "checkpoint_selected_expansion_decision": checkpoint_summary.get("selected_expansion_decision"),
                "scoring_review_disposition": scoring_summary.get("selected_review_disposition"),
                "credible_external_path_signal_present": scoring_summary.get("credible_external_path_signal_present"),
                "hold_scope_interpretation": resolution_contract.get("hold_scope_interpretation"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_lane": target_lane,
            "hold_rule": checkpoint_summary.get("hold_policy"),
            "hold_scope_interpretation": resolution_contract.get("hold_scope_interpretation"),
            "next_action": next_action,
            "single_layer_only": bool(resolution_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(resolution_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "tgc93_branch_decision_package": _ptr(tgc93_path),
            "cosmo_sr_seam_authorization_activation_decision_report": _ptr(phase2_decision_path),
            "discovery_queue_transition_decision_report": _ptr(transition_path),
            "discovery_engine_review_checkpoint_report": _ptr(checkpoint_path),
            "discovery_engine_scoring_routing_review_report": _ptr(scoring_review_path),
        },
        "non_claim_boundary": "Repository-local COSMO-SR discovery-review hold resolution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the COSMO-SR discovery-review hold resolution report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "cosmo_sr_discovery_review_hold_resolution_20260418_v0.json",
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
        "cosmo_sr_discovery_review_hold_resolution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())