from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_20260412_v0.json"
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
    decision_policy = dict(declaration.get("decision_policy", {}))
    decision_contract = dict(declaration.get("decision_contract", {}))

    phase_d_selection_path = REPO_ROOT / str(
        required_inputs.get("science_phase_d_untouched_lane_selection_report", "")
    ).strip()
    first_test_path = REPO_ROOT / str(
        required_inputs.get("science_phase_d_untouched_lane_first_test_packet_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_d_selection = _read_json(phase_d_selection_path)
    first_test = _read_json(first_test_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_d_selection_outcome = str(
        dict(phase_d_selection.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    selected_lane = str(
        dict(phase_d_selection.get("summary", {})).get("untouched_lane_candidate_id", "")
    ).strip()
    first_test_outcome = str(dict(first_test.get("summary", {})).get("terminal_outcome", "")).strip()
    first_test_attack_class = str(
        dict(first_test.get("summary", {})).get("single_attack_class", "")
    ).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_d_selection_outcome = str(decision_policy.get("required_phase_d_selection_outcome", "")).strip()
    required_phase_d_first_test_outcome = str(decision_policy.get("required_phase_d_first_test_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        decision_policy.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_selected_untouched_lane = str(
        decision_policy.get("required_selected_untouched_lane", "")
    ).strip()

    target_lane = str(decision_policy.get("target_lane", "")).strip()
    selected_attack_class = str(decision_policy.get("selected_attack_class", "")).strip()

    first_test_under_specified = bool(decision_policy.get("first_test_under_specified", False))
    first_test_local_weakness_identified = bool(
        decision_policy.get("first_test_local_weakness_identified", False)
    )
    current_attack_class_exhausted = bool(decision_policy.get("current_attack_class_exhausted", False))
    path_falsification_evidence_detected = bool(
        decision_policy.get("path_falsification_evidence_detected", False)
    )
    continue_requires_explicit_authorization = bool(
        decision_policy.get("continue_requires_explicit_authorization", True)
    )

    preconditions_ok = (
        phase_d_selection_outcome == required_phase_d_selection_outcome
        and first_test_outcome == required_phase_d_first_test_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and selected_lane == required_selected_untouched_lane
        and selected_lane == target_lane
        and bool(selected_attack_class)
        and first_test_attack_class == selected_attack_class
        and continue_requires_explicit_authorization
    )

    allowed_outcomes = set(decision_contract.get("allowed_outcomes", []))
    default_outcome = str(
        decision_contract.get("default_outcome", "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE"
        next_action = "REPAIR_PHASE_E_PRECONDITIONS_AND_RERUN_DECISION_LAYER"
    elif path_falsification_evidence_detected:
        terminal_outcome = "UNTOUCHED_LANE_PATH_FALSIFIED"
        next_action = "CLOSE_UNTOUCHED_LANE_AND_RETURN_TO_SELECTION_GOVERNANCE"
    elif first_test_local_weakness_identified and not current_attack_class_exhausted:
        terminal_outcome = "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED"
        next_action = "OPEN_ONE_BOUNDED_SIGNAL_REFINEMENT_LAYER_ONLY"
    elif first_test_under_specified and current_attack_class_exhausted:
        terminal_outcome = "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS"
        next_action = "OPEN_ONE_BOUNDED_ATTACK_CLASS_RESELECTION_LAYER_ONLY"
    else:
        terminal_outcome = "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE"
        next_action = "STOP_AND_HOLD_UNTIL_NEW_EVIDENCE_OR_POLICY_AUTHORIZATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_d_selection_outcome_match": phase_d_selection_outcome == required_phase_d_selection_outcome,
            "phase_d_first_test_outcome_match": first_test_outcome == required_phase_d_first_test_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "selected_lane_match": selected_lane == required_selected_untouched_lane,
            "selected_lane_matches_target": selected_lane == target_lane,
            "selected_attack_class_declared": bool(selected_attack_class),
            "selected_attack_class_matches_first_test": first_test_attack_class == selected_attack_class,
            "continue_requires_explicit_authorization": continue_requires_explicit_authorization,
            "single_terminal_outcome_rule_declared": str(
                decision_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_OUTCOME",
            "no_loop_rule_declared": str(decision_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "decision_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_d_selection_outcome": phase_d_selection_outcome,
                "required_phase_d_selection_outcome": required_phase_d_selection_outcome,
                "first_test_outcome": first_test_outcome,
                "required_phase_d_first_test_outcome": required_phase_d_first_test_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "selected_lane": selected_lane,
                "required_selected_untouched_lane": required_selected_untouched_lane,
                "target_lane": target_lane,
                "selected_attack_class": selected_attack_class,
                "first_test_attack_class": first_test_attack_class,
                "first_test_under_specified": first_test_under_specified,
                "first_test_local_weakness_identified": first_test_local_weakness_identified,
                "current_attack_class_exhausted": current_attack_class_exhausted,
                "path_falsification_evidence_detected": path_falsification_evidence_detected,
                "continue_requires_explicit_authorization": continue_requires_explicit_authorization,
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
            "single_layer_only": bool(decision_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(decision_policy.get("single_outcome_only", True)),
            "continue_authorized": terminal_outcome
            in {
                "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED",
                "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS",
            },
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_d_untouched_lane_selection_report": _ptr(phase_d_selection_path),
            "science_phase_d_untouched_lane_first_test_packet_report": _ptr(first_test_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local untouched-lane post-first-test decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase E untouched-lane post-first-test decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_e_untouched_lane_post_first_test_decision_20260412_v0.json",
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
        "science_phase_e_untouched_lane_post_first_test_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
