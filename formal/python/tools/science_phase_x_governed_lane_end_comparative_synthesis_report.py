from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_20260412_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("governed_lane_end_synthesis_contract", {}))
    outcome_contract = dict(declaration.get("governed_lane_end_synthesis_outcome_contract", {}))

    phase_w_path = REPO_ROOT / str(
        required_inputs.get("science_phase_w_pre_execution_plateau_decision_report", "")
    ).strip()
    phase_j_path = REPO_ROOT / str(
        required_inputs.get("science_phase_j_untouched_lane_post_refinement_decision_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_w = _read_json(phase_w_path)
    phase_j = _read_json(phase_j_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_w_summary = dict(phase_w.get("summary", {}))
    phase_j_summary = dict(phase_j.get("summary", {}))
    non_reopen_summary_summary = dict(non_reopen_summary.get("summary", {}))

    phase_w_outcome = str(phase_w_summary.get("terminal_outcome", "")).strip()
    phase_w_authorized_lane_id = str(phase_w_summary.get("authorized_lane_id", "")).strip()
    phase_w_packet_authorization = bool(phase_w_summary.get("authorize_first_test_packet", True))

    phase_j_outcome = str(phase_j_summary.get("terminal_outcome", "")).strip()
    phase_j_target_lane = str(phase_j_summary.get("target_lane", "")).strip()

    non_reopen_summary_outcome = str(non_reopen_summary_summary.get("terminal_outcome", "")).strip()
    non_reopen_reasons = dict(non_reopen_summary.get("closed_lane_non_reopen_reasons", {}))

    required_phase_w_outcome = str(contract.get("required_phase_w_outcome", "")).strip()
    required_phase_w_authorized_lane_id = str(contract.get("required_phase_w_authorized_lane_id", "")).strip()
    required_phase_w_packet_authorization = bool(contract.get("required_phase_w_packet_authorization", False))
    required_phase_j_outcome = str(contract.get("required_phase_j_outcome", "")).strip()
    required_phase_j_target_lane = str(contract.get("required_phase_j_target_lane", "")).strip()
    required_non_reopen_summary_outcome = str(contract.get("required_non_reopen_summary_outcome", "")).strip()
    required_closed_lane_ids = list(contract.get("required_closed_lane_ids", []))

    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    signals = dict(contract.get("synthesis_signals", {}))
    lane_end_family_complete = bool(signals.get("lane_end_family_complete", False))
    thermal_lane_marked_preserved_inactive = bool(
        signals.get("thermal_lane_marked_preserved_inactive", False)
    )
    thermal_lane_further_closure_prohibited = bool(
        signals.get("thermal_lane_further_closure_prohibited", False)
    )
    thermal_lane_packet_prohibited = bool(signals.get("thermal_lane_packet_prohibited", False))
    project_level_synthesis_only = bool(signals.get("project_level_synthesis_only", False))
    policy_revision_evaluation_required = bool(
        signals.get("policy_revision_evaluation_required", False)
    )
    force_policy_escalation_now = bool(signals.get("force_policy_escalation_now", False))

    signals_shape_ok = all(
        key in signals
        for key in [
            "lane_end_family_complete",
            "thermal_lane_marked_preserved_inactive",
            "thermal_lane_further_closure_prohibited",
            "thermal_lane_packet_prohibited",
            "project_level_synthesis_only",
            "policy_revision_evaluation_required",
            "force_policy_escalation_now",
        ]
    )

    closed_lane_coverage_ok = all(lane in non_reopen_reasons for lane in required_closed_lane_ids)

    preconditions_ok = (
        phase_w_outcome == required_phase_w_outcome
        and phase_w_authorized_lane_id == required_phase_w_authorized_lane_id
        and phase_w_packet_authorization == required_phase_w_packet_authorization
        and phase_j_outcome == required_phase_j_outcome
        and phase_j_target_lane == required_phase_j_target_lane
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and closed_lane_coverage_ok
        and forbid_reopen
        and signals_shape_ok
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "GOVERNED_LANE_END_SYNTHESIS_EVIDENCE_INCOMPLETE")
    ).strip()

    if not signals_shape_ok:
        terminal_outcome = "HOLD_PENDING_GOVERNED_LANE_END_SYNTHESIS_REPAIR"
        next_action = "REPAIR_GOVERNED_LANE_END_SYNTHESIS_SIGNAL_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "GOVERNED_LANE_END_SYNTHESIS_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_X_PRECONDITIONS_AND_RERUN"
    elif force_policy_escalation_now:
        terminal_outcome = "ESCALATE_TO_HIGHER_LEVEL_POLICY_FOR_FUTURE_CANDIDATE_SELECTION"
        next_action = "ESCALATE_POLICY_BEFORE_ANY_NEW_FUTURE_CANDIDATE_MATURATION"
    else:
        terminal_outcome = "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE"
        next_action = "OPEN_ONE_BOUNDED_POLICY_DECISION_LAYER_OR_WAIT_FOR_STRONGER_CANDIDATE_CLASS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    governed_lane_end_states = {
        "QM-STAT": {
            "classification": "VALID_BUT_NONMOVING_POLICY_INCOMPLETE",
            "reason": non_reopen_reasons.get("QM-STAT", ""),
        },
        "GR-ROW-001": {
            "classification": "VALID_BUT_NONMOVING_REQUIRES_NEW_STRUCTURE",
            "reason": non_reopen_reasons.get("GR-ROW-001", ""),
        },
        "EM-QFT": {
            "classification": "VALID_BUT_NONMOVING_REQUIRES_NEW_STRUCTURE",
            "reason": non_reopen_reasons.get("EM-QFT", ""),
        },
        "SHARED-MODEL-CLASS": {
            "classification": "EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
            "reason": non_reopen_reasons.get("SHARED-MODEL-CLASS", ""),
        },
        "QFT-GR": {
            "classification": "EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
            "reason": non_reopen_reasons.get("QFT-GR", ""),
        },
        required_phase_j_target_lane: {
            "classification": "VALID_BUT_NONMOVING_PRESERVED_INACTIVE",
            "reason": "Phase J terminal outcome locked as valid-but-nonmoving.",
        },
        required_phase_w_authorized_lane_id: {
            "classification": "NEAR_READY_BUT_NOT_EXECUTABLE_PRESERVED_INACTIVE",
            "reason": "Phase W terminal outcome locked as near-ready but not executable.",
            "phase_w_terminal_outcome": phase_w_outcome,
            "further_closure_authorized": False,
            "packet_authorized": False,
        },
    }

    category_counts = {
        "externally_comparable_but_not_probe_ready": 2,
        "valid_but_nonmoving": 3,
        "near_ready_but_not_executable": 1,
        "valid_but_nonmoving_policy_incomplete": 1,
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_w_outcome_match": phase_w_outcome == required_phase_w_outcome,
            "phase_w_authorized_lane_id_match": phase_w_authorized_lane_id == required_phase_w_authorized_lane_id,
            "phase_w_packet_authorization_match": phase_w_packet_authorization
            == required_phase_w_packet_authorization,
            "phase_j_outcome_match": phase_j_outcome == required_phase_j_outcome,
            "phase_j_target_lane_match": phase_j_target_lane == required_phase_j_target_lane,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome
            == required_non_reopen_summary_outcome,
            "required_closed_lane_coverage_ok": closed_lane_coverage_ok,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "synthesis_signal_shape_ok": signals_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "governed_lane_end_synthesis_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_w_outcome": phase_w_outcome,
                "required_phase_w_outcome": required_phase_w_outcome,
                "phase_w_authorized_lane_id": phase_w_authorized_lane_id,
                "required_phase_w_authorized_lane_id": required_phase_w_authorized_lane_id,
                "phase_w_packet_authorization": phase_w_packet_authorization,
                "required_phase_w_packet_authorization": required_phase_w_packet_authorization,
                "phase_j_outcome": phase_j_outcome,
                "required_phase_j_outcome": required_phase_j_outcome,
                "phase_j_target_lane": phase_j_target_lane,
                "required_phase_j_target_lane": required_phase_j_target_lane,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "governed_lane_end_states": governed_lane_end_states,
        "category_counts": category_counts,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "thermal_boundary_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
            "thermal_boundary_no_further_closure_authorized": thermal_lane_further_closure_prohibited,
            "thermal_boundary_packet_authorized": False,
            "future_candidate_maturation_authorized_now": False,
            "policy_revision_evaluation_required": policy_revision_evaluation_required,
            "project_level_synthesis_only": project_level_synthesis_only,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "synthesis_signals": signals,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_w_pre_execution_plateau_decision_report": _ptr(phase_w_path),
            "science_phase_j_untouched_lane_post_refinement_decision_report": _ptr(phase_j_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local governed lane-end comparative synthesis report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase X governed lane-end comparative synthesis report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_x_governed_lane_end_comparative_synthesis_20260412_v0.json",
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
        "science_phase_x_governed_lane_end_comparative_synthesis_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
