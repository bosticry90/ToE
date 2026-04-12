from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_20260412_v0.json"
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
    policy_contract = dict(declaration.get("policy_contract", {}))
    selection_policy_contract = dict(declaration.get("selection_policy_contract", {}))

    phase_k_path = REPO_ROOT / str(
        required_inputs.get("science_phase_k_new_lane_design_criteria_synthesis_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_k = _read_json(phase_k_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_k_summary = dict(phase_k.get("summary", {}))
    phase_k_outcome = str(phase_k_summary.get("terminal_outcome", "")).strip()
    phase_k_resume_mode = str(phase_k_summary.get("recommend_resume_mode", "")).strip()

    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_k_outcome = str(policy_contract.get("required_phase_k_outcome", "")).strip()
    required_phase_k_resume_mode = str(policy_contract.get("required_phase_k_resume_mode", "")).strip()
    required_non_reopen_summary_outcome = str(
        policy_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()

    lane_discriminativity_prerequisites = list(policy_contract.get("lane_discriminativity_prerequisites", []))
    acceptable_attack_class_properties = list(
        policy_contract.get("acceptable_first_test_attack_class_properties", [])
    )
    nonmoving_early_warning_signals = list(policy_contract.get("nonmoving_early_warning_signals", []))
    exclude_low_yield_when = list(policy_contract.get("exclude_likely_low_yield_lanes_when", []))

    required_lane_end_state_family_size = int(policy_contract.get("required_lane_end_state_family_size", 0))
    lane_end_state_family_actual_size = 6

    forbid_reopen = bool(policy_contract.get("forbid_closed_or_held_lane_reopen", False))
    forbid_packet_before_gate = bool(
        policy_contract.get("forbid_new_untouched_lane_packet_before_policy_gate", False)
    )

    policy_shape_ok = (
        len(lane_discriminativity_prerequisites) >= 3
        and len(acceptable_attack_class_properties) >= 3
        and len(nonmoving_early_warning_signals) >= 3
        and len(exclude_low_yield_when) >= 3
    )

    preconditions_ok = (
        phase_k_outcome == required_phase_k_outcome
        and phase_k_resume_mode == required_phase_k_resume_mode
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and lane_end_state_family_actual_size >= required_lane_end_state_family_size
        and forbid_reopen
        and forbid_packet_before_gate
        and policy_shape_ok
    )

    allowed_outcomes = set(selection_policy_contract.get("allowed_outcomes", []))
    default_outcome = str(
        selection_policy_contract.get("default_outcome", "HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE")
    ).strip()

    if required_lane_end_state_family_size < 6:
        terminal_outcome = "HOLD_PENDING_SELECTION_POLICY_REPAIR"
        next_action = "REPAIR_LANE_END_STATE_FAMILY_COVERAGE_REQUIREMENT"
    elif not preconditions_ok:
        terminal_outcome = "HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_L_PRECONDITIONS_AND_RERUN"
    else:
        terminal_outcome = "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED"
        next_action = "USE_POLICY_LANE_TO_GOVERN_NEXT_UNTOUCHED_LANE_AUTHORIZATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    policy_payload = {
        "minimum_lane_discriminativity_prerequisites": lane_discriminativity_prerequisites,
        "acceptable_first_test_attack_class_properties": acceptable_attack_class_properties,
        "nonmoving_early_warning_signals": nonmoving_early_warning_signals,
        "exclude_likely_low_yield_lanes_when": exclude_low_yield_when,
        "new_untouched_lane_packet_authorization": "DENY_UNTIL_POLICY_GATE_APPLIED",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_k_outcome_match": phase_k_outcome == required_phase_k_outcome,
            "phase_k_resume_mode_match": phase_k_resume_mode == required_phase_k_resume_mode,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "lane_end_state_family_coverage_ok": lane_end_state_family_actual_size
            >= required_lane_end_state_family_size,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "forbid_new_untouched_lane_packet_before_policy_gate": forbid_packet_before_gate,
            "policy_shape_complete": policy_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                selection_policy_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_OUTCOME",
            "no_loop_rule_declared": str(
                selection_policy_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "selection_policy_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_k_outcome": phase_k_outcome,
                "required_phase_k_outcome": required_phase_k_outcome,
                "phase_k_resume_mode": phase_k_resume_mode,
                "required_phase_k_resume_mode": required_phase_k_resume_mode,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "lane_end_state_family_actual_size": lane_end_state_family_actual_size,
                "required_lane_end_state_family_size": required_lane_end_state_family_size,
                "forbid_closed_or_held_lane_reopen": forbid_reopen,
                "forbid_new_untouched_lane_packet_before_policy_gate": forbid_packet_before_gate,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "higher_level_selection_policy": policy_payload,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
            "authorize_new_untouched_lane_packet": False,
            "next_action": next_action,
            "single_layer_only": bool(policy_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(policy_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_k_new_lane_design_criteria_synthesis_report": _ptr(phase_k_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local higher-level lane-selection policy report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase L higher-level selection-policy report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_l_higher_level_selection_policy_20260412_v0.json",
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
        "science_phase_l_higher_level_selection_policy_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_new_untouched_lane_packet={payload['summary']['authorize_new_untouched_lane_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
