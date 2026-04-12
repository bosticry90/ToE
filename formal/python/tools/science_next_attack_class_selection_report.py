from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_NEXT_ATTACK_CLASS_SELECTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_NEXT_ATTACK_CLASS_SELECTION_20260411_v0.json"
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
    selection_policy = dict(declaration.get("selection_policy", {}))

    science_baseline_path = REPO_ROOT / str(required_inputs.get("science_global_completion_baseline_report", ""))
    proof_debt_decision_path = REPO_ROOT / str(required_inputs.get("proof_debt_program_exhaustion_decision_report", ""))
    qm_ruling_path = REPO_ROOT / str(required_inputs.get("qm_blocker_moving_ruling_report", ""))

    science_baseline = _read_json(science_baseline_path)
    proof_debt_decision = _read_json(proof_debt_decision_path)
    qm_ruling = _read_json(qm_ruling_path)

    completion_assessment = dict(science_baseline.get("completion_assessment", {}))
    proof_debt_summary = dict(proof_debt_decision.get("summary", {}))
    qm_ruling_summary = dict(qm_ruling.get("summary", {}))

    science_incomplete = not bool(completion_assessment.get("science_global_complete", False))
    proof_debt_exhausted = (
        str(proof_debt_summary.get("program_state", "")).strip()
        == "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
    )
    qm_ruling_token = str(qm_ruling_summary.get("qm_ruling", "")).strip()
    do_not_reopen_proof_debt_in_parallel = bool(selection_policy.get("do_not_reopen_proof_debt_in_parallel", False))

    selected_next_attack_class = None
    if qm_ruling_token == str(selection_policy.get("retain_qm_when_ruling", "")).strip():
        decision = "RETAIN_QM_AS_ACTIVE_BLOCKER_ROW"
        next_action = "CONTINUE_QM_BLOCKER_MOVING_PROGRAM"
    elif science_incomplete and proof_debt_exhausted and qm_ruling_token in {
        "EXHAUSTED_UNDER_CURRENT_FILTER",
        "VALID_BUT_NONMOVING",
    }:
        decision = "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS"
        selected_next_attack_class = str(selection_policy.get("default_next_attack_class", "")).strip() or None
        next_action = str(selection_policy.get("default_next_action", "")).strip() or (
            "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET"
        )
    else:
        decision = "SELECTION_INCOMPLETE"
        next_action = "REVIEW_QM_RULING_AND_SCIENCE_STATE_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "science_state_present": science_baseline_path.exists(),
            "proof_debt_decision_present": proof_debt_decision_path.exists(),
            "qm_ruling_present": qm_ruling_path.exists(),
            "science_incomplete": science_incomplete,
            "proof_debt_exhausted": proof_debt_exhausted,
            "selection_policy_declared": bool(selection_policy),
        },
        "objective_quality": {
            "criteria": {
                "retain_qm_route_supported": qm_ruling_token == "MOVING",
                "escalation_route_supported": (
                    science_incomplete
                    and proof_debt_exhausted
                    and qm_ruling_token in {"EXHAUSTED_UNDER_CURRENT_FILTER", "VALID_BUT_NONMOVING"}
                ),
                "proof_debt_not_reopened_in_parallel": do_not_reopen_proof_debt_in_parallel,
                "decision_materialized": decision in {
                    "RETAIN_QM_AS_ACTIVE_BLOCKER_ROW",
                    "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS",
                    "SELECTION_INCOMPLETE",
                },
            },
            "inputs": {
                "science_global_complete": completion_assessment.get("science_global_complete"),
                "global_objective_complete": completion_assessment.get("global_objective_complete"),
                "proof_debt_program_state": proof_debt_summary.get("program_state"),
                "proof_debt_decision": proof_debt_summary.get("decision"),
                "qm_ruling": qm_ruling_token,
                "default_next_attack_class": selection_policy.get("default_next_attack_class"),
                "default_next_action": selection_policy.get("default_next_action"),
                "do_not_reopen_proof_debt_in_parallel": do_not_reopen_proof_debt_in_parallel,
            },
            "summary": {
                "all_criteria_satisfied": decision != "SELECTION_INCOMPLETE",
                "phase_status": "COMPLETE" if decision != "SELECTION_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "decision": decision,
            "selected_next_attack_class": selected_next_attack_class,
            "next_action": next_action,
            "proof_debt_parallel_reopen_allowed": not do_not_reopen_proof_debt_in_parallel,
            "qm_ruling": qm_ruling_token,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_global_completion_baseline_report": _ptr(science_baseline_path),
            "proof_debt_program_exhaustion_decision_report": _ptr(proof_debt_decision_path),
            "qm_blocker_moving_ruling_report": _ptr(qm_ruling_path),
        },
        "non_claim_boundary": "Repository-local science next attack-class selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate science next attack-class selection report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_next_attack_class_selection_20260411_v0.json",
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
        "science_next_attack_class_selection_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
