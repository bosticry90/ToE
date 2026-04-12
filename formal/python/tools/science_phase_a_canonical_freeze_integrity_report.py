from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_20260412_v0.json"
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
    integrity_policy = dict(declaration.get("integrity_policy", {}))
    integrity_contract = dict(declaration.get("integrity_contract", {}))

    frontier_path = REPO_ROOT / str(required_inputs.get("science_multi_lane_frontier_consolidation_report", "")).strip()
    synthesis_path = REPO_ROOT / str(required_inputs.get("science_common_failure_modes_synthesis_report", "")).strip()
    probe_path = REPO_ROOT / str(required_inputs.get("probe_readiness_standard_candidate_report", "")).strip()
    selection_path = REPO_ROOT / str(required_inputs.get("science_restart_mode_selection_report", "")).strip()

    frontier = _read_json(frontier_path)
    synthesis = _read_json(synthesis_path)
    probe = _read_json(probe_path)
    selection = _read_json(selection_path)

    frontier_outcome = str(dict(frontier.get("summary", {})).get("terminal_outcome", "")).strip()
    synthesis_outcome = str(dict(synthesis.get("summary", {})).get("terminal_outcome", "")).strip()
    probe_outcome = str(dict(probe.get("summary", {})).get("terminal_outcome", "")).strip()
    selection_outcome = str(dict(selection.get("summary", {})).get("terminal_outcome", "")).strip()

    required_frontier_outcome = str(integrity_policy.get("required_frontier_outcome", "")).strip()
    required_synthesis_outcome = str(integrity_policy.get("required_synthesis_outcome", "")).strip()
    allowed_probe_outcomes = set(integrity_policy.get("allowed_probe_candidate_outcomes", []))
    allowed_selection_outcomes = set(integrity_policy.get("allowed_restart_selection_outcomes", []))
    blocked_selection_outcomes = set(integrity_policy.get("blocked_restart_selection_outcomes", []))

    preconditions_ok = (
        frontier_outcome == required_frontier_outcome
        and synthesis_outcome == required_synthesis_outcome
        and probe_outcome in allowed_probe_outcomes
    )

    allowed_outcomes = set(integrity_contract.get("allowed_outcomes", []))
    default_outcome = str(
        integrity_contract.get("default_outcome", "PHASE_A_CANONICAL_FREEZE_INTEGRITY_INCOMPLETE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "PHASE_A_CANONICAL_FREEZE_INTEGRITY_INCOMPLETE"
        next_action = "RESTORE_PHASE_A_PRECONDITIONS_AND_RERUN_INTEGRITY_LAYER"
    elif selection_outcome in blocked_selection_outcomes:
        terminal_outcome = "PHASE_A_CANONICAL_FREEZE_RESTART_CONTRACT_VIOLATION"
        next_action = "REPAIR_RESTART_SELECTION_CONTRACT_AND_RERUN"
    elif selection_outcome not in allowed_selection_outcomes:
        terminal_outcome = "PHASE_A_CANONICAL_FREEZE_HOLD_PENDING_REPAIR"
        next_action = "HOLD_AND_REPAIR_RESTART_SELECTION_OUTCOME"
    else:
        terminal_outcome = "PHASE_A_CANONICAL_FREEZE_INTEGRITY_CONFIRMED"
        next_action = "PHASE_A_OBJECTIVE_QUALITY_COMPLETE_PROCEED_TO_PHASE_C_EXECUTION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "frontier_outcome_match": frontier_outcome == required_frontier_outcome,
            "synthesis_outcome_match": synthesis_outcome == required_synthesis_outcome,
            "probe_candidate_outcome_match": probe_outcome in allowed_probe_outcomes,
            "restart_selection_outcome_allowed": selection_outcome in allowed_selection_outcomes,
            "restart_selection_outcome_not_blocked": selection_outcome not in blocked_selection_outcomes,
            "single_terminal_outcome_rule_declared": str(
                integrity_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_OUTCOME",
            "no_loop_rule_declared": str(integrity_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "phase_a_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "frontier_outcome": frontier_outcome,
                "required_frontier_outcome": required_frontier_outcome,
                "synthesis_outcome": synthesis_outcome,
                "required_synthesis_outcome": required_synthesis_outcome,
                "probe_candidate_outcome": probe_outcome,
                "allowed_probe_candidate_outcomes": sorted(allowed_probe_outcomes),
                "restart_selection_outcome": selection_outcome,
                "allowed_restart_selection_outcomes": sorted(allowed_selection_outcomes),
                "blocked_restart_selection_outcomes": sorted(blocked_selection_outcomes),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(integrity_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(integrity_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_multi_lane_frontier_consolidation_report": _ptr(frontier_path),
            "science_common_failure_modes_synthesis_report": _ptr(synthesis_path),
            "probe_readiness_standard_candidate_report": _ptr(probe_path),
            "science_restart_mode_selection_report": _ptr(selection_path),
        },
        "non_claim_boundary": "Repository-local Phase A canonical-freeze integrity report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Phase A canonical-freeze integrity report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_phase_a_canonical_freeze_integrity_20260412_v0.json",
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
        "science_phase_a_canonical_freeze_integrity_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
