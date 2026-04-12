from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROGRAM_POSTURE_REVIEW_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROGRAM_POSTURE_REVIEW_PACKET_20260411_v0.json"
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
    posture_policy = dict(declaration.get("posture_policy", {}))
    review_questions = list(declaration.get("review_questions", []))

    decision_path = REPO_ROOT / str(
        required_inputs.get("science_post_architecture_alignment_decision_report", "")
    )
    ruling_path = REPO_ROOT / str(
        required_inputs.get("architecture_seam_master_action_alignment_ruling_report", "")
    )
    diagnosis_path = REPO_ROOT / str(
        required_inputs.get("architecture_level_blocker_diagnosis_packet_report", "")
    )

    decision_report = _read_json(decision_path)
    ruling_report = _read_json(ruling_path)
    diagnosis_report = _read_json(diagnosis_path)

    decision_summary = dict(decision_report.get("summary", {}))
    ruling_summary = dict(ruling_report.get("summary", {}))
    diagnosis_summary = dict(diagnosis_report.get("summary", {}))

    # Derive posture signals from upstream artifacts
    post_architecture_decision = str(
        decision_summary.get("post_architecture_decision", "")
    ).strip()
    selected_next_program_mode_from_decision = str(
        decision_summary.get("selected_next_program_mode", "")
    ).strip()
    alignment_ruling = str(ruling_summary.get("alignment_ruling", "")).strip()
    blocker_conversion_failure_location = str(
        diagnosis_summary.get("blocker_conversion_failure_location", "")
    ).strip()

    # Policy parameters
    nonmoving_threshold = int(
        posture_policy.get("nonmoving_attack_class_count_threshold", 4)
    )
    observed_nonmoving = list(
        posture_policy.get("observed_nonmoving_attack_classes", [])
    )
    blocker_movement_ever_observed = bool(
        posture_policy.get("blocker_movement_ever_observed", False)
    )
    formal_org_outpacing_default = bool(
        posture_policy.get("formal_organization_outpacing_conversion_default", True)
    )
    measurement_fit_default = bool(
        posture_policy.get("measurement_regime_fit_for_purpose_default", True)
    )
    default_next_program_mode = str(
        posture_policy.get("default_next_program_mode", "")
    ).strip() or "REORIENT_MEASUREMENT_REGIME"
    no_loop_rule = str(posture_policy.get("no_loop_rule", "")).strip()
    no_further_policy = str(
        posture_policy.get("no_further_attack_packets_policy", "")
    ).strip()

    # Q1: Is the measurement regime still fit for purpose?
    nonmoving_count = len(observed_nonmoving)
    measurement_regime_fit_for_purpose = (
        measurement_fit_default
        if blocker_movement_ever_observed
        else nonmoving_count < nonmoving_threshold
    )
    q1_answer = (
        "MEASUREMENT_REGIME_FIT_FOR_PURPOSE"
        if measurement_regime_fit_for_purpose
        else "MEASUREMENT_REGIME_REQUIRES_REVISION"
    )

    # Q2: Is formal organization outpacing scientific conversion?
    formal_org_outpacing = (
        formal_org_outpacing_default
        if not blocker_movement_ever_observed
        else False
    )
    q2_answer = (
        "FORMAL_ORGANIZATION_OUTPACING_SCIENTIFIC_CONVERSION"
        if formal_org_outpacing
        else "SCIENTIFIC_CONVERSION_PACING_ACCEPTABLE"
    )

    # Q3: One bounded next program mode
    if not measurement_regime_fit_for_purpose:
        q3_answer = "REORIENT_MEASUREMENT_REGIME"
    elif formal_org_outpacing:
        q3_answer = "REORIENT_PROGRAM_EXECUTION_MODEL"
    else:
        q3_answer = default_next_program_mode

    # Derive review answers
    review_answers = [
        {"question_id": "Q1", "answer": q1_answer},
        {"question_id": "Q2", "answer": q2_answer},
        {"question_id": "Q3", "answer": q3_answer},
    ]

    posture_review_complete = post_architecture_decision == "PROGRAM_POSTURE_REVIEW_REQUIRED"
    packet_outcome = (
        "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED"
        if posture_review_complete
        else "PROGRAM_POSTURE_REVIEW_PACKET_INCOMPLETE"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "post_architecture_decision_is_posture_review": posture_review_complete,
            "nonmoving_attack_class_count_at_threshold": nonmoving_count >= nonmoving_threshold,
            "blocker_movement_ever_observed": blocker_movement_ever_observed,
            "measurement_regime_fit_for_purpose": measurement_regime_fit_for_purpose,
            "formal_organization_outpacing_conversion": formal_org_outpacing,
            "no_loop_rule_declared": no_loop_rule == "ONE_POSTURE_REVIEW_ONLY",
            "no_further_attack_packets_enforced": (
                no_further_policy == "NO_FURTHER_ATTACK_PACKETS_UNTIL_POSTURE_RESOLVED"
            ),
        },
        "objective_quality": {
            "criteria": {
                "all_three_review_questions_answered": len(review_answers) == 3,
                "q1_measurement_regime_answered": q1_answer
                in {
                    "MEASUREMENT_REGIME_FIT_FOR_PURPOSE",
                    "MEASUREMENT_REGIME_REQUIRES_REVISION",
                },
                "q2_formal_org_answered": q2_answer
                in {
                    "FORMAL_ORGANIZATION_OUTPACING_SCIENTIFIC_CONVERSION",
                    "SCIENTIFIC_CONVERSION_PACING_ACCEPTABLE",
                },
                "q3_next_program_mode_answered": q3_answer
                in {
                    "REORIENT_MEASUREMENT_REGIME",
                    "REORIENT_ARCHITECTURE_TARGET_SELECTION",
                    "REORIENT_PROGRAM_EXECUTION_MODEL",
                },
                "packet_outcome_materialized": packet_outcome
                == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED",
            },
            "inputs": {
                "review_questions": review_questions,
                "review_answers": review_answers,
                "post_architecture_decision": post_architecture_decision,
                "selected_next_program_mode_from_decision": selected_next_program_mode_from_decision,
                "alignment_ruling": alignment_ruling,
                "blocker_conversion_failure_location": blocker_conversion_failure_location,
                "observed_nonmoving_attack_classes": observed_nonmoving,
                "nonmoving_attack_class_count": nonmoving_count,
                "nonmoving_count_threshold": nonmoving_threshold,
                "blocker_movement_ever_observed": blocker_movement_ever_observed,
                "no_loop_rule": no_loop_rule,
                "no_further_attack_packets_policy": no_further_policy,
            },
            "summary": {
                "all_criteria_satisfied": posture_review_complete,
                "phase_status": "COMPLETE" if posture_review_complete else "INCOMPLETE",
                "next_action": "EXECUTE_POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION",
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "measurement_regime_fit_for_purpose": measurement_regime_fit_for_purpose,
            "formal_organization_outpacing_conversion": formal_org_outpacing,
            "selected_next_program_mode": q3_answer,
            "no_loop_rule": no_loop_rule,
            "next_action": "EXECUTE_POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_post_architecture_alignment_decision_report": _ptr(decision_path),
            "architecture_seam_master_action_alignment_ruling_report": _ptr(ruling_path),
            "architecture_level_blocker_diagnosis_packet_report": _ptr(diagnosis_path),
        },
        "non_claim_boundary": "Repository-local program posture review packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the program posture review packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "program_posture_review_packet_20260411_v0.json",
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
        "program_posture_review_packet_report: "
        f"outcome={payload['summary']['packet_outcome']} "
        f"next_program_mode={payload['summary']['selected_next_program_mode']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
