from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_20260412_v0.json"
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


def _group_complete(group: list[str]) -> bool:
    return len(group) >= 3 and all(bool(str(item).strip()) for item in group)


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    activation_contract = dict(declaration.get("activation_contract", {}))
    activation_outcome_contract = dict(declaration.get("activation_outcome_contract", {}))

    phase_l_path = REPO_ROOT / str(
        required_inputs.get("science_phase_l_higher_level_selection_policy_report", "")
    ).strip()
    phase_k_path = REPO_ROOT / str(
        required_inputs.get("science_phase_k_new_lane_design_criteria_synthesis_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_l = _read_json(phase_l_path)
    phase_k = _read_json(phase_k_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_l_summary = dict(phase_l.get("summary", {}))
    phase_k_summary = dict(phase_k.get("summary", {}))

    phase_l_outcome = str(phase_l_summary.get("terminal_outcome", "")).strip()
    phase_l_resume_mode = str(phase_l_summary.get("resume_mode", "")).strip()
    phase_l_authorize_packet = bool(phase_l_summary.get("authorize_new_untouched_lane_packet", True))

    phase_k_outcome = str(phase_k_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_l_outcome = str(activation_contract.get("required_phase_l_outcome", "")).strip()
    required_phase_l_resume_mode = str(activation_contract.get("required_phase_l_resume_mode", "")).strip()
    required_phase_l_authorize_packet = bool(
        activation_contract.get("required_phase_l_authorize_packet", False)
    )
    required_phase_k_outcome = str(activation_contract.get("required_phase_k_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        activation_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()

    forbid_reopen = bool(activation_contract.get("forbid_closed_or_held_lane_reopen", False))

    thresholds = dict(activation_contract.get("activation_criteria_thresholds", {}))
    minimum_discriminativity_prerequisites = list(
        thresholds.get("minimum_discriminativity_prerequisites", [])
    )
    minimum_attack_class_admissibility = list(
        thresholds.get("minimum_attack_class_admissibility", [])
    )
    minimum_observable_interface_specificity = list(
        thresholds.get("minimum_observable_interface_specificity", [])
    )
    minimum_anti_alias_confidence = list(thresholds.get("minimum_anti_alias_confidence", []))
    authorize_flip_rule = str(thresholds.get("authorize_flip_rule", "")).strip()

    groups_complete = (
        _group_complete(minimum_discriminativity_prerequisites)
        and _group_complete(minimum_attack_class_admissibility)
        and _group_complete(minimum_observable_interface_specificity)
        and _group_complete(minimum_anti_alias_confidence)
    )

    preconditions_ok = (
        phase_l_outcome == required_phase_l_outcome
        and phase_l_resume_mode == required_phase_l_resume_mode
        and phase_l_authorize_packet == required_phase_l_authorize_packet
        and phase_k_outcome == required_phase_k_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and groups_complete
        and authorize_flip_rule == "AUTHORIZE_ONLY_WHEN_ALL_CRITERIA_GROUPS_SATISFIED"
    )

    allowed_outcomes = set(activation_outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        activation_outcome_contract.get("default_outcome", "SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE")
    ).strip()

    if not groups_complete:
        terminal_outcome = "HOLD_PENDING_ACTIVATION_CRITERIA_REPAIR"
        next_action = "REPAIR_ACTIVATION_CRITERIA_GROUP_COVERAGE"
    elif not preconditions_ok:
        terminal_outcome = "SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_M_PRECONDITIONS_AND_RERUN"
    else:
        terminal_outcome = "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED"
        next_action = "KEEP_AUTHORIZATION_DENY_UNTIL_FUTURE_LANE_MEETS_ALL_PHASE_M_CRITERIA"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_l_outcome_match": phase_l_outcome == required_phase_l_outcome,
            "phase_l_resume_mode_match": phase_l_resume_mode == required_phase_l_resume_mode,
            "phase_l_authorize_packet_match": phase_l_authorize_packet == required_phase_l_authorize_packet,
            "phase_k_outcome_match": phase_k_outcome == required_phase_k_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome
            == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "criteria_groups_complete": groups_complete,
            "authorize_flip_rule_declared": authorize_flip_rule
            == "AUTHORIZE_ONLY_WHEN_ALL_CRITERIA_GROUPS_SATISFIED",
            "single_terminal_outcome_rule_declared": str(
                activation_outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_OUTCOME",
            "no_loop_rule_declared": str(
                activation_outcome_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "activation_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_l_outcome": phase_l_outcome,
                "required_phase_l_outcome": required_phase_l_outcome,
                "phase_l_resume_mode": phase_l_resume_mode,
                "required_phase_l_resume_mode": required_phase_l_resume_mode,
                "phase_l_authorize_packet": phase_l_authorize_packet,
                "required_phase_l_authorize_packet": required_phase_l_authorize_packet,
                "phase_k_outcome": phase_k_outcome,
                "required_phase_k_outcome": required_phase_k_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "activation_criteria": {
            "minimum_discriminativity_prerequisites": minimum_discriminativity_prerequisites,
            "minimum_attack_class_admissibility": minimum_attack_class_admissibility,
            "minimum_observable_interface_specificity": minimum_observable_interface_specificity,
            "minimum_anti_alias_confidence": minimum_anti_alias_confidence,
            "authorize_flip_rule": authorize_flip_rule,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
            "authorize_new_untouched_lane_packet": False,
            "next_action": next_action,
            "single_layer_only": bool(activation_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(activation_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_l_higher_level_selection_policy_report": _ptr(phase_l_path),
            "science_phase_k_new_lane_design_criteria_synthesis_report": _ptr(phase_k_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local selection-policy activation criteria report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase M selection-policy activation-criteria report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_m_selection_policy_activation_criteria_20260412_v0.json",
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
        "science_phase_m_selection_policy_activation_criteria_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_new_untouched_lane_packet={payload['summary']['authorize_new_untouched_lane_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
