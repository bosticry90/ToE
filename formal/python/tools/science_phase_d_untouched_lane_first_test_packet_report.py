from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_20260412_v0.json"
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


def _norm(value: str) -> str:
    return value.strip().upper().replace("_", "-")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    first_test_policy = dict(declaration.get("first_test_policy", {}))
    first_test_contract = dict(declaration.get("first_test_contract", {}))

    phase_d_path = REPO_ROOT / str(required_inputs.get("science_phase_d_untouched_lane_selection_report", "")).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()
    reopen_eligibility_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_reopen_eligibility_report", "")
    ).strip()

    phase_d = _read_json(phase_d_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)
    reopen_eligibility = _read_json(reopen_eligibility_path)

    phase_d_outcome = str(dict(phase_d.get("summary", {})).get("terminal_outcome", "")).strip()
    selected_lane = str(dict(phase_d.get("summary", {})).get("untouched_lane_candidate_id", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    reopen_eligibility_outcome = str(
        dict(reopen_eligibility.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_d_selection_outcome = str(first_test_policy.get("required_phase_d_selection_outcome", "")).strip()
    required_selected_untouched_lane = str(first_test_policy.get("required_selected_untouched_lane", "")).strip()
    required_non_reopen_summary_outcome = str(
        first_test_policy.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_reopen_eligibility_outcome = str(
        first_test_policy.get("required_reopen_eligibility_outcome", "")
    ).strip()

    target_lane = str(first_test_policy.get("target_lane", "")).strip()
    single_attack_class = str(first_test_policy.get("single_attack_class", "")).strip()
    one_execution_only = bool(first_test_policy.get("one_execution_only", False))
    one_immediate_ruling_only = bool(first_test_policy.get("one_immediate_ruling_only", False))
    first_test_signal_detected = bool(first_test_policy.get("first_test_signal_detected", False))

    anti_alias_checks = dict(first_test_policy.get("anti_alias_checks", {}))
    anti_alias_coverage_ok = set(anti_alias_checks.keys()) == _CANONICAL_CLOSED_LANES
    anti_alias_all_true = anti_alias_coverage_ok and all(bool(v) for v in anti_alias_checks.values())

    target_lane_is_consumed_alias = _norm(target_lane) in {_norm(x) for x in _CANONICAL_CLOSED_LANES}
    selected_lane_matches_target = selected_lane == target_lane

    preconditions_ok = (
        phase_d_outcome == required_phase_d_selection_outcome
        and selected_lane == required_selected_untouched_lane
        and selected_lane_matches_target
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and reopen_eligibility_outcome == required_reopen_eligibility_outcome
        and anti_alias_all_true
        and not target_lane_is_consumed_alias
        and bool(single_attack_class)
    )

    allowed_outcomes = set(first_test_contract.get("allowed_outcomes", []))
    default_outcome = str(
        first_test_contract.get("default_outcome", "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION"
        next_action = "REPAIR_FIRST_TEST_PRECONDITIONS_AND_RERUN_SINGLE_PACKET"
    elif not one_execution_only or not one_immediate_ruling_only:
        terminal_outcome = "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION"
        next_action = "RESTORE_ONE_EXECUTION_AND_ONE_IMMEDIATE_RULING_CONSTRAINTS"
    elif first_test_signal_detected:
        terminal_outcome = "UNTOUCHED_LANE_FIRST_TEST_SIGNAL_DETECTED"
        next_action = "OPEN_ONE_POST_SIGNAL_INTERPRETATION_LAYER_ONLY"
    else:
        terminal_outcome = "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD"
        next_action = "STOP_AND_INTERPRET_BEFORE_ANY_WIDENING"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_d_selection_outcome_match": phase_d_outcome == required_phase_d_selection_outcome,
            "selected_lane_match": selected_lane == required_selected_untouched_lane,
            "selected_lane_matches_target": selected_lane_matches_target,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "reopen_eligibility_outcome_match": reopen_eligibility_outcome == required_reopen_eligibility_outcome,
            "anti_alias_coverage_ok": anti_alias_coverage_ok,
            "anti_alias_all_true": anti_alias_all_true,
            "target_lane_is_not_consumed_alias": not target_lane_is_consumed_alias,
            "single_attack_class_declared": bool(single_attack_class),
            "single_terminal_outcome_rule_declared": str(
                first_test_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_OUTCOME",
            "no_loop_rule_declared": str(first_test_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "first_test_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_d_selection_outcome": phase_d_outcome,
                "required_phase_d_selection_outcome": required_phase_d_selection_outcome,
                "selected_lane": selected_lane,
                "required_selected_untouched_lane": required_selected_untouched_lane,
                "target_lane": target_lane,
                "single_attack_class": single_attack_class,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "reopen_eligibility_outcome": reopen_eligibility_outcome,
                "required_reopen_eligibility_outcome": required_reopen_eligibility_outcome,
                "anti_alias_checks": anti_alias_checks,
                "one_execution_only": one_execution_only,
                "one_immediate_ruling_only": one_immediate_ruling_only,
                "first_test_signal_detected": first_test_signal_detected,
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
            "single_attack_class": single_attack_class,
            "next_action": next_action,
            "single_layer_only": bool(first_test_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(first_test_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_d_untouched_lane_selection_report": _ptr(phase_d_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
            "science_closed_lane_reopen_eligibility_report": _ptr(reopen_eligibility_path),
        },
        "non_claim_boundary": "Repository-local untouched-lane first-test packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Phase D untouched-lane first-test packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_d_untouched_lane_first_test_packet_20260412_v0.json",
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
        "science_phase_d_untouched_lane_first_test_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
