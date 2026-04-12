from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_BLOCKER_MOVING_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_BLOCKER_MOVING_RULING_20260411_v0.json"
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
    ruling_policy = dict(declaration.get("ruling_policy", {}))

    qm_blocker_moving_packet_path = REPO_ROOT / str(required_inputs.get("qm_blocker_moving_packet", ""))
    qm_blocker_moving_tranche_report_path = REPO_ROOT / str(required_inputs.get("qm_blocker_moving_tranche_report", ""))

    qm_blocker_moving_packet = _read_json(qm_blocker_moving_packet_path)
    qm_blocker_moving_tranche_report = _read_json(qm_blocker_moving_tranche_report_path)

    summary = dict(qm_blocker_moving_tranche_report.get("summary", {}))
    tranche_classification = str(summary.get("tranche_classification", "")).strip()
    no_loop_rule = str(summary.get("no_loop_rule", "")).strip()
    row_id = str(summary.get("row_id", "")).strip()
    subtarget_id = str(summary.get("subtarget_id", "")).strip()
    exclude_from_immediate_reselection = False

    if tranche_classification == "QM_BLOCKER_MOVED":
        qm_ruling = "MOVING"
        next_action = "CONTINUE_QM_BLOCKER_MOVING_PROGRAM"
    elif tranche_classification == "QM_VALID_BUT_NONMOVING" and no_loop_rule == "ONE_BOUNDED_EXECUTION_ONLY":
        qm_ruling = "EXHAUSTED_UNDER_CURRENT_FILTER"
        exclude_from_immediate_reselection = True
        next_action = str(ruling_policy.get("next_action_if_exhausted", "")).strip() or (
            "REFRESH_ATTACK_CLASS_SELECTION_AND_DO_NOT_LOOP_QM"
        )
    elif tranche_classification == "QM_VALID_BUT_NONMOVING":
        qm_ruling = "VALID_BUT_NONMOVING"
        next_action = "REVIEW_QM_SELECTION_POLICY_ONCE"
    else:
        qm_ruling = "RULING_INCOMPLETE"
        next_action = "RESTORE_QM_RULING_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_present": qm_blocker_moving_packet_path.exists(),
            "tranche_report_present": qm_blocker_moving_tranche_report_path.exists(),
            "tranche_classification_materialized": tranche_classification in {
                "QM_BLOCKER_MOVED",
                "QM_VALID_BUT_NONMOVING",
                "QM_TRANCHE_INCOMPLETE",
            },
            "single_execution_no_loop_rule_declared": no_loop_rule == "ONE_BOUNDED_EXECUTION_ONLY",
            "ruling_materialized": qm_ruling != "RULING_INCOMPLETE",
        },
        "objective_quality": {
            "criteria": {
                "moving_rule_supported": tranche_classification == "QM_BLOCKER_MOVED",
                "valid_but_nonmoving_rule_supported": tranche_classification == "QM_VALID_BUT_NONMOVING",
                "exhaustion_rule_supported": (
                    tranche_classification == "QM_VALID_BUT_NONMOVING"
                    and no_loop_rule == "ONE_BOUNDED_EXECUTION_ONLY"
                ),
                "immediate_reselection_excluded_when_exhausted": (
                    qm_ruling != "EXHAUSTED_UNDER_CURRENT_FILTER" or exclude_from_immediate_reselection
                ),
            },
            "inputs": {
                "tranche_classification": tranche_classification,
                "row_id": row_id,
                "subtarget_id": subtarget_id,
                "no_loop_rule": no_loop_rule,
                "moving_rule": ruling_policy.get("moving_rule"),
                "valid_but_nonmoving_rule": ruling_policy.get("valid_but_nonmoving_rule"),
                "exhaustion_rule": ruling_policy.get("exhaustion_rule"),
            },
            "summary": {
                "all_criteria_satisfied": qm_ruling != "RULING_INCOMPLETE",
                "phase_status": "COMPLETE" if qm_ruling != "RULING_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "row_id": row_id,
            "subtarget_id": subtarget_id,
            "qm_ruling": qm_ruling,
            "tranche_classification": tranche_classification,
            "exclude_from_immediate_reselection": exclude_from_immediate_reselection,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qm_blocker_moving_packet": _ptr(qm_blocker_moving_packet_path),
            "qm_blocker_moving_tranche_report": _ptr(qm_blocker_moving_tranche_report_path),
        },
        "non_claim_boundary": "Repository-local QM blocker-moving ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM blocker-moving ruling report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_blocker_moving_ruling_20260411_v0.json",
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
        "qm_blocker_moving_ruling_report: "
        f"qm_ruling={payload['summary']['qm_ruling']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
