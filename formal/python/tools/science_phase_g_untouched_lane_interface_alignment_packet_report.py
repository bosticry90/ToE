from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
)

_CANONICAL_CLOSED_LANES = {
    "QM-STAT",
    "GR-ROW-001",
    "EM-QFT",
    "SHARED-MODEL-CLASS",
    "QFT-GR",
}


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
    packet_policy = dict(declaration.get("packet_policy", {}))
    packet_contract = dict(declaration.get("packet_contract", {}))

    phase_d_selection_path = REPO_ROOT / str(
        required_inputs.get("science_phase_d_untouched_lane_selection_report", "")
    ).strip()
    phase_f_reselection_path = REPO_ROOT / str(
        required_inputs.get("science_phase_f_untouched_lane_attack_class_reselection_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_d_selection = _read_json(phase_d_selection_path)
    phase_f_reselection = _read_json(phase_f_reselection_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_d_selection_outcome = str(
        dict(phase_d_selection.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    phase_d_selected_lane = str(
        dict(phase_d_selection.get("summary", {})).get("untouched_lane_candidate_id", "")
    ).strip()

    phase_f_reselection_outcome = str(
        dict(phase_f_reselection.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    phase_f_selected_attack_class = str(
        dict(phase_f_reselection.get("summary", {})).get("selected_next_attack_class", "")
    ).strip()

    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_d_selection_outcome = str(packet_policy.get("required_phase_d_selection_outcome", "")).strip()
    required_phase_f_reselection_outcome = str(packet_policy.get("required_phase_f_reselection_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        packet_policy.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_selected_untouched_lane = str(packet_policy.get("required_selected_untouched_lane", "")).strip()
    required_selected_attack_class = str(packet_policy.get("required_selected_attack_class", "")).strip()

    target_lane = str(packet_policy.get("target_lane", "")).strip()
    selected_attack_class = str(packet_policy.get("selected_attack_class", "")).strip()

    one_execution_only = bool(packet_policy.get("one_execution_only", False))
    one_immediate_ruling_only = bool(packet_policy.get("one_immediate_ruling_only", False))
    signal_detected = bool(packet_policy.get("signal_detected", False))
    alignment_valid_without_movement = bool(packet_policy.get("alignment_valid_without_movement", False))
    undeclared_structure_detected = bool(packet_policy.get("undeclared_structure_detected", False))

    anti_alias_checks = dict(packet_policy.get("anti_alias_checks", {}))
    anti_alias_coverage_ok = set(anti_alias_checks.keys()) == _CANONICAL_CLOSED_LANES
    anti_alias_all_true = anti_alias_coverage_ok and all(bool(v) for v in anti_alias_checks.values())

    preconditions_ok = (
        phase_d_selection_outcome == required_phase_d_selection_outcome
        and phase_f_reselection_outcome == required_phase_f_reselection_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and phase_d_selected_lane == required_selected_untouched_lane
        and phase_d_selected_lane == target_lane
        and phase_f_selected_attack_class == required_selected_attack_class
        and selected_attack_class == required_selected_attack_class
        and anti_alias_all_true
    )

    allowed_outcomes = set(packet_contract.get("allowed_outcomes", []))
    default_outcome = str(packet_contract.get("default_outcome", "UNTOUCHED_LANE_PATH_FALSIFIED")).strip()

    if not preconditions_ok or not one_execution_only or not one_immediate_ruling_only:
        terminal_outcome = "UNTOUCHED_LANE_PATH_FALSIFIED"
        next_action = "STOP_AND_REPAIR_PHASE_G_CONTRACT_BEFORE_ANY_RETRY"
    elif undeclared_structure_detected:
        terminal_outcome = "UNTOUCHED_LANE_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "STOP_AND_ROUTE_TO_STRUCTURE_DECLARATION_LAYER"
    elif signal_detected:
        terminal_outcome = "UNTOUCHED_LANE_SIGNAL_PRODUCED"
        next_action = "STOP_AND_OPEN_ONE_POST_SIGNAL_INTERPRETATION_LAYER_ONLY"
    elif alignment_valid_without_movement:
        terminal_outcome = "UNTOUCHED_LANE_VALID_BUT_NONMOVING"
        next_action = "STOP_AND_INTERPRET_BEFORE_ANY_WIDENING"
    else:
        terminal_outcome = "UNTOUCHED_LANE_PATH_FALSIFIED"
        next_action = "STOP_AND_REASSESS_LANE_VIABILITY"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_d_selection_outcome_match": phase_d_selection_outcome == required_phase_d_selection_outcome,
            "phase_f_reselection_outcome_match": phase_f_reselection_outcome == required_phase_f_reselection_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "selected_lane_match": phase_d_selected_lane == required_selected_untouched_lane,
            "selected_lane_matches_target": phase_d_selected_lane == target_lane,
            "selected_attack_class_match": phase_f_selected_attack_class == required_selected_attack_class,
            "packet_selected_attack_class_match": selected_attack_class == required_selected_attack_class,
            "anti_alias_coverage_ok": anti_alias_coverage_ok,
            "anti_alias_all_true": anti_alias_all_true,
            "single_terminal_outcome_rule_declared": str(
                packet_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_OUTCOME",
            "no_loop_rule_declared": str(packet_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "packet_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_d_selection_outcome": phase_d_selection_outcome,
                "required_phase_d_selection_outcome": required_phase_d_selection_outcome,
                "phase_f_reselection_outcome": phase_f_reselection_outcome,
                "required_phase_f_reselection_outcome": required_phase_f_reselection_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "selected_lane": phase_d_selected_lane,
                "required_selected_untouched_lane": required_selected_untouched_lane,
                "target_lane": target_lane,
                "phase_f_selected_attack_class": phase_f_selected_attack_class,
                "required_selected_attack_class": required_selected_attack_class,
                "packet_selected_attack_class": selected_attack_class,
                "one_execution_only": one_execution_only,
                "one_immediate_ruling_only": one_immediate_ruling_only,
                "signal_detected": signal_detected,
                "alignment_valid_without_movement": alignment_valid_without_movement,
                "undeclared_structure_detected": undeclared_structure_detected,
                "anti_alias_checks": anti_alias_checks,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_lane": target_lane,
            "selected_attack_class": selected_attack_class,
            "next_action": next_action,
            "single_layer_only": bool(packet_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(packet_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_d_untouched_lane_selection_report": _ptr(phase_d_selection_path),
            "science_phase_f_untouched_lane_attack_class_reselection_report": _ptr(phase_f_reselection_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local untouched-lane interface-alignment packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase G untouched-lane interface-alignment packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_g_untouched_lane_interface_alignment_packet_20260412_v0.json",
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
        "science_phase_g_untouched_lane_interface_alignment_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" selected_attack_class={payload['summary']['selected_attack_class']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
