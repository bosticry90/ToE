from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION_20260411_v0.json"
)

_VALID_DEFECT_ANSWERS = {
    "BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS",
    "BLOCKER_MOVEMENT_SIGNAL_DEFINITION_TOO_NARROW_FOR_SEAM_LEVEL_WORK",
    "NO_OBSERVABLE_CONVERSION_UNIT_IN_CURRENT_SIGNAL_SET",
}
_VALID_NEW_SIGNAL_ANSWERS = {
    "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
    "ARCHITECTURE_BINDING_UNIT_COVERAGE_DELTA_GT_0",
    "TRANSPORT_WITNESS_BINDING_COVERAGE_DELTA_GT_0",
}
_VALID_RETAINED_SIGNAL_ANSWERS = {
    "THEOREM_GAP_DELTA_LT_0_REMAINS_AUTHORITATIVE",
    "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
    "ALL_PRIOR_SIGNALS_DEPRECATED_UNDER_REVISED_REGIME",
}
_VALID_PILOT_ANSWERS = {
    "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS",
    "ONE_ARCHITECTURE_BINDING_UNIT_UNDER_REVISED_SIGNALS",
    "ONE_TRANSPORT_WITNESS_COVERAGE_INCREMENT_UNDER_REVISED_SIGNALS",
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
    transition_policy = dict(declaration.get("transition_policy", {}))
    transition_questions = list(declaration.get("transition_questions", []))
    selected_next_program_mode = str(
        declaration.get("selected_next_program_mode", "")
    ).strip()
    triggered_by = str(declaration.get("triggered_by", "")).strip()

    posture_path = REPO_ROOT / str(
        required_inputs.get("program_posture_review_packet_report", "")
    )
    posture_report = _read_json(posture_path)
    posture_summary = dict(posture_report.get("summary", {}))

    # Confirm the posture review mandates this transition
    posture_outcome = str(posture_summary.get("packet_outcome", "")).strip()
    posture_program_mode = str(posture_summary.get("selected_next_program_mode", "")).strip()
    transition_triggered = (
        posture_outcome == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED"
        and posture_program_mode == "REORIENT_MEASUREMENT_REGIME"
    )

    # Pull policy answers
    measurement_defect_answer = str(
        transition_policy.get("measurement_defect_answer", "")
    ).strip()
    new_signal_answer = str(transition_policy.get("new_signal_answer", "")).strip()
    retained_signal_answer = str(transition_policy.get("retained_signal_answer", "")).strip()
    pilot_tranche_answer = str(transition_policy.get("pilot_tranche_answer", "")).strip()
    no_loop_rule = str(transition_policy.get("no_loop_rule", "")).strip()
    no_broad_rewrite_policy = str(transition_policy.get("no_broad_rewrite_policy", "")).strip()
    reversibility_rule = str(transition_policy.get("reversibility_rule", "")).strip()

    q1_valid = measurement_defect_answer in _VALID_DEFECT_ANSWERS
    q2_valid = new_signal_answer in _VALID_NEW_SIGNAL_ANSWERS
    q3_valid = retained_signal_answer in _VALID_RETAINED_SIGNAL_ANSWERS
    q4_valid = pilot_tranche_answer in _VALID_PILOT_ANSWERS
    all_questions_answered = q1_valid and q2_valid and q3_valid and q4_valid

    transition_answers = [
        {"question_id": "Q1", "answer": measurement_defect_answer},
        {"question_id": "Q2", "answer": new_signal_answer},
        {"question_id": "Q3", "answer": retained_signal_answer},
        {"question_id": "Q4", "answer": pilot_tranche_answer},
    ]

    if transition_triggered and all_questions_answered:
        transition_outcome = "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED"
        next_action = "EXECUTE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONCE"
    else:
        transition_outcome = "MEASUREMENT_REGIME_TRANSITION_INCOMPLETE"
        next_action = "RESTORE_TRANSITION_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "selected_next_program_mode": selected_next_program_mode,
        "triggered_by": triggered_by,
        "criteria": {
            "posture_review_outcome_materialized": posture_outcome
            == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED",
            "posture_review_mode_is_reorient_measurement_regime": posture_program_mode
            == "REORIENT_MEASUREMENT_REGIME",
            "transition_triggered": transition_triggered,
            "q1_measurement_defect_answered": q1_valid,
            "q2_new_signal_answered": q2_valid,
            "q3_retained_signal_answered": q3_valid,
            "q4_pilot_tranche_answered": q4_valid,
            "all_transition_questions_answered": all_questions_answered,
            "no_loop_rule_declared": no_loop_rule == "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
            "bounded_single_tranche_policy_declared": bool(no_broad_rewrite_policy),
            "reversibility_rule_declared": bool(reversibility_rule),
        },
        "objective_quality": {
            "criteria": {
                "transition_outcome_materialized": transition_outcome
                == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED",
                "measurement_defect_explicit": q1_valid,
                "new_signal_explicit": q2_valid,
                "retained_signal_explicit": q3_valid,
                "pilot_tranche_bounded": q4_valid,
            },
            "inputs": {
                "transition_questions": transition_questions,
                "transition_answers": transition_answers,
                "posture_review_outcome": posture_outcome,
                "posture_review_selected_mode": posture_program_mode,
                "measurement_defect": measurement_defect_answer,
                "new_blocker_movement_signal": new_signal_answer,
                "retained_blocker_movement_signal": retained_signal_answer,
                "pilot_tranche": pilot_tranche_answer,
                "no_loop_rule": no_loop_rule,
                "no_broad_rewrite_policy": no_broad_rewrite_policy,
                "reversibility_rule": reversibility_rule,
            },
            "summary": {
                "all_criteria_satisfied": transition_outcome
                == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED",
                "phase_status": "COMPLETE"
                if transition_outcome == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "transition_outcome": transition_outcome,
            "measurement_defect": measurement_defect_answer,
            "new_blocker_movement_signal": new_signal_answer,
            "retained_blocker_movement_signal": retained_signal_answer,
            "pilot_tranche": pilot_tranche_answer,
            "no_loop_rule": no_loop_rule,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "program_posture_review_packet_report": _ptr(posture_path),
        },
        "non_claim_boundary": "Repository-local post-posture-review program mode transition report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-posture-review program mode transition report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "post_posture_review_program_mode_transition_20260411_v0.json",
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
        "post_posture_review_program_mode_transition_report: "
        f"outcome={payload['summary']['transition_outcome']} "
        f"pilot={payload['summary']['pilot_tranche']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
