from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_RESTART_MODE_SELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_RESTART_MODE_SELECTION_20260412_v0.json"
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


def _normalized(value: str) -> str:
    return value.strip().upper().replace("_", "-")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    selection_policy = dict(declaration.get("selection_policy", {}))
    selection_contract = dict(declaration.get("selection_contract", {}))

    synthesis_path = REPO_ROOT / str(required_inputs.get("science_common_failure_modes_synthesis_report", "")).strip()
    probe_path = REPO_ROOT / str(required_inputs.get("probe_readiness_standard_candidate_report", "")).strip()

    synthesis = _read_json(synthesis_path)
    probe = _read_json(probe_path)

    synthesis_outcome = str(dict(synthesis.get("summary", {})).get("terminal_outcome", "")).strip()
    probe_outcome = str(dict(probe.get("summary", {})).get("terminal_outcome", "")).strip()

    required_synthesis_outcome = str(selection_policy.get("required_synthesis_outcome", "")).strip()
    allowed_probe_standard_outcomes = set(selection_policy.get("allowed_probe_standard_outcomes", []))

    allowed_restart_modes = set(selection_policy.get("allowed_restart_modes", []))
    selected_restart_mode = str(selection_policy.get("selected_restart_mode", "")).strip()

    policy_lane_id = str(selection_policy.get("policy_lane_id", "")).strip()
    untouched_lane_candidate_id = str(selection_policy.get("untouched_lane_candidate_id", "")).strip()
    untouched_lane_non_consumption_proof_declared = bool(
        selection_policy.get("untouched_lane_non_consumption_proof_declared", False)
    )

    consumed_lane_aliases = list(selection_policy.get("consumed_lane_aliases", []))
    consumed_alias_set = {_normalized(alias) for alias in consumed_lane_aliases}

    preconditions_ok = (
        synthesis_outcome == required_synthesis_outcome
        and probe_outcome in allowed_probe_standard_outcomes
        and selected_restart_mode in allowed_restart_modes
    )

    untouched_alias_blocked = _normalized(untouched_lane_candidate_id) in consumed_alias_set

    allowed_outcomes = set(selection_contract.get("allowed_outcomes", []))
    default_outcome = str(
        selection_contract.get("default_outcome", "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_REQUIRED_INPUTS_AND_RERUN_RESTART_MODE_SELECTION"
    elif selected_restart_mode == "GENUINELY_UNTOUCHED_LANE" and untouched_alias_blocked:
        terminal_outcome = "RESTART_MODE_SELECTION_BLOCKED_CONSUMED_LANE_ALIAS"
        next_action = "SELECT_NEW_UNTOUCHED_LANE_WITH_NON_CONSUMPTION_PROOF"
    elif selected_restart_mode == "GENUINELY_UNTOUCHED_LANE" and not untouched_lane_non_consumption_proof_declared:
        terminal_outcome = "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE"
        next_action = "DECLARE_UNTOUCHED_LANE_NON_CONSUMPTION_PROOF"
    elif selected_restart_mode == "GENUINELY_UNTOUCHED_LANE":
        terminal_outcome = "RESTART_MODE_SELECTED_UNTOUCHED_LANE"
        next_action = "OPEN_ONE_BOUNDED_UNTOUCHED_LANE_SELECTION_EXECUTION_LAYER"
    else:
        terminal_outcome = "RESTART_MODE_SELECTED_POLICY_LANE"
        next_action = "OPEN_ONE_BOUNDED_POLICY_EVIDENCE_STANDARD_LANE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "synthesis_outcome_match": synthesis_outcome == required_synthesis_outcome,
            "probe_standard_outcome_match": probe_outcome in allowed_probe_standard_outcomes,
            "selected_restart_mode_allowed": selected_restart_mode in allowed_restart_modes,
            "untouched_alias_not_consumed": not untouched_alias_blocked,
            "untouched_non_consumption_proof_declared": untouched_lane_non_consumption_proof_declared,
            "single_terminal_outcome_rule_declared": str(
                selection_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_RESTART_MODE_SELECTION_OUTCOME",
            "no_loop_rule_declared": str(selection_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_RESTART_MODE_SELECTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "selection_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "synthesis_outcome": synthesis_outcome,
                "required_synthesis_outcome": required_synthesis_outcome,
                "probe_standard_outcome": probe_outcome,
                "allowed_probe_standard_outcomes": sorted(allowed_probe_standard_outcomes),
                "selected_restart_mode": selected_restart_mode,
                "allowed_restart_modes": sorted(allowed_restart_modes),
                "policy_lane_id": policy_lane_id,
                "untouched_lane_candidate_id": untouched_lane_candidate_id,
                "untouched_lane_non_consumption_proof_declared": untouched_lane_non_consumption_proof_declared,
                "consumed_lane_aliases": consumed_lane_aliases,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "selected_restart_mode": selected_restart_mode,
            "next_action": next_action,
            "single_layer_only": bool(selection_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(selection_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_common_failure_modes_synthesis_report": _ptr(synthesis_path),
            "probe_readiness_standard_candidate_report": _ptr(probe_path),
        },
        "non_claim_boundary": "Repository-local restart-mode selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate restart-mode selection report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_restart_mode_selection_20260412_v0.json",
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
        "science_restart_mode_selection_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
