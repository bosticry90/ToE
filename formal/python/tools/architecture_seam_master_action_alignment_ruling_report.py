from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING_20260411_v0.json"
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

    execution_path = REPO_ROOT / str(
        required_inputs.get("architecture_seam_master_action_alignment_packet_execution", "")
    )
    execution_report_path = REPO_ROOT / str(
        required_inputs.get("architecture_seam_master_action_alignment_packet_execution_report", "")
    )

    execution = _read_json(execution_path)
    execution_report = _read_json(execution_report_path)

    execution_summary = dict(execution_report.get("summary", {}))
    execution_classification = str(execution_summary.get("execution_classification", "")).strip()
    no_loop_rule = str(execution_summary.get("no_loop_rule", "")).strip()

    if execution_classification == "ARCHITECTURE_ALIGNMENT_MOVED":
        alignment_ruling = "MOVING"
        next_action = "CONTINUE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ROUTE"
    elif (
        execution_classification == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"
        and no_loop_rule == "ONE_BOUNDED_EXECUTION_ONLY"
    ):
        alignment_ruling = "EXHAUSTED_UNDER_CURRENT_FILTER"
        next_action = str(ruling_policy.get("next_action_if_exhausted", "")).strip() or (
            "REVIEW_POST_ARCHITECTURE_ALIGNMENT_DECISION_AND_DO_NOT_LOOP_ALIGNMENT_PACKET"
        )
    elif execution_classification == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING":
        alignment_ruling = "VALID_BUT_NONMOVING"
        next_action = "REVIEW_ALIGNMENT_SELECTION_POLICY_ONCE"
    else:
        alignment_ruling = "RULING_INCOMPLETE"
        next_action = "RESTORE_ALIGNMENT_RULING_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_declaration_present": execution_path.exists(),
            "execution_report_present": execution_report_path.exists(),
            "execution_classification_materialized": execution_classification
            in {
                "ARCHITECTURE_ALIGNMENT_MOVED",
                "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "ARCHITECTURE_ALIGNMENT_INCOMPLETE",
            },
            "single_execution_no_loop_rule_declared": no_loop_rule == "ONE_BOUNDED_EXECUTION_ONLY",
            "ruling_materialized": alignment_ruling != "RULING_INCOMPLETE",
        },
        "objective_quality": {
            "criteria": {
                "moving_rule_supported": execution_classification == "ARCHITECTURE_ALIGNMENT_MOVED",
                "valid_but_nonmoving_rule_supported": execution_classification
                == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "exhaustion_rule_supported": execution_classification
                == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"
                and no_loop_rule == "ONE_BOUNDED_EXECUTION_ONLY",
            },
            "inputs": {
                "execution_classification": execution_classification,
                "bridge_object_materialized": execution_summary.get("bridge_object_materialized"),
                "alignment_witness_bound": execution_summary.get("alignment_witness_bound"),
                "target_row_recompute_triggered": execution_summary.get("target_row_recompute_triggered"),
                "blocker_movement_signal_true": execution_summary.get("blocker_movement_signal_true"),
                "no_loop_rule": no_loop_rule,
                "moving_rule": ruling_policy.get("moving_rule"),
                "valid_but_nonmoving_rule": ruling_policy.get("valid_but_nonmoving_rule"),
                "exhaustion_rule": ruling_policy.get("exhaustion_rule"),
            },
            "summary": {
                "all_criteria_satisfied": alignment_ruling != "RULING_INCOMPLETE",
                "phase_status": "COMPLETE" if alignment_ruling != "RULING_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "alignment_ruling": alignment_ruling,
            "execution_classification": execution_classification,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "execution_declaration": _ptr(execution_path),
            "execution_report": _ptr(execution_report_path),
        },
        "non_claim_boundary": "Repository-local architecture seam/master-action alignment ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate architecture seam/master-action alignment ruling report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "architecture_seam_master_action_alignment_ruling_20260411_v0.json",
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
        "architecture_seam_master_action_alignment_ruling_report: "
        f"alignment_ruling={payload['summary']['alignment_ruling']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
