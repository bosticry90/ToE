from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROBE_READINESS_STANDARD_FORMALIZATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_FORMALIZATION_20260412_v0.json"
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
    formalization_policy = dict(declaration.get("formalization_policy", {}))
    formalization_contract = dict(declaration.get("formalization_contract", {}))

    synthesis_path = REPO_ROOT / str(required_inputs.get("science_common_failure_modes_synthesis_report", "")).strip()
    candidate_path = REPO_ROOT / str(required_inputs.get("probe_readiness_standard_candidate_report", "")).strip()
    selection_path = REPO_ROOT / str(required_inputs.get("science_restart_mode_selection_report", "")).strip()

    synthesis = _read_json(synthesis_path)
    candidate = _read_json(candidate_path)
    selection = _read_json(selection_path)

    synthesis_outcome = str(dict(synthesis.get("summary", {})).get("terminal_outcome", "")).strip()
    candidate_outcome = str(dict(candidate.get("summary", {})).get("terminal_outcome", "")).strip()
    selection_outcome = str(dict(selection.get("summary", {})).get("terminal_outcome", "")).strip()

    required_synthesis_outcome = str(formalization_policy.get("required_synthesis_outcome", "")).strip()
    allowed_candidate_outcomes = set(formalization_policy.get("allowed_candidate_outcomes", []))
    required_selection_outcome = str(formalization_policy.get("required_restart_selection_outcome", "")).strip()

    required_standard_keys = list(formalization_policy.get("required_standard_keys", []))
    candidate_standard = dict(candidate.get("probe_readiness_standard_candidate", {}))
    standard_keys_complete = all(
        key in candidate_standard and candidate_standard.get(key) not in ("", None, [])
        for key in required_standard_keys
    )

    transition_levels_required_exact = list(formalization_policy.get("transition_levels_required_exact", []))
    transition_levels = list(candidate_standard.get("transition_levels", []))
    transition_levels_match = transition_levels == transition_levels_required_exact

    enforce_non_reopen = bool(formalization_policy.get("enforce_non_reopen_during_formalization", True))
    selected_restart_mode = str(dict(selection.get("summary", {})).get("selected_restart_mode", "")).strip()
    non_reopen_ok = (not enforce_non_reopen) or selected_restart_mode == "NEW_POLICY_EVIDENCE_STANDARD_LANE"

    preconditions_ok = (
        synthesis_outcome == required_synthesis_outcome
        and candidate_outcome in allowed_candidate_outcomes
        and selection_outcome == required_selection_outcome
        and standard_keys_complete
        and transition_levels_match
        and non_reopen_ok
    )

    allowed_outcomes = set(formalization_contract.get("allowed_outcomes", []))
    default_outcome = str(
        formalization_contract.get("default_outcome", "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE"
        next_action = "RESTORE_FORMALIZATION_PRECONDITIONS_AND_RERUN"
    elif not non_reopen_ok:
        terminal_outcome = "PROBE_READINESS_STANDARD_FORMALIZATION_CONTRACT_VIOLATION"
        next_action = "REASSERT_POLICY_LANE_NON_REOPEN_POSTURE"
    elif not standard_keys_complete or not transition_levels_match:
        terminal_outcome = "HOLD_PENDING_POLICY_REPAIR"
        next_action = "REPAIR_STANDARD_FIELDS_AND_TRANSITION_LEVELS"
    else:
        terminal_outcome = "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED"
        next_action = "OPEN_ONE_BOUNDED_CLOSED_LANE_REOPEN_ELIGIBILITY_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "synthesis_outcome_match": synthesis_outcome == required_synthesis_outcome,
            "candidate_outcome_match": candidate_outcome in allowed_candidate_outcomes,
            "restart_selection_outcome_match": selection_outcome == required_selection_outcome,
            "standard_keys_complete": standard_keys_complete,
            "transition_levels_match": transition_levels_match,
            "non_reopen_policy_match": non_reopen_ok,
            "single_terminal_outcome_rule_declared": str(
                formalization_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_PROBE_READINESS_STANDARD_FORMALIZATION_OUTCOME",
            "no_loop_rule_declared": str(formalization_contract.get("no_loop_rule", "")).strip()
            == "ONE_PROBE_READINESS_STANDARD_FORMALIZATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "formalization_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "synthesis_outcome": synthesis_outcome,
                "required_synthesis_outcome": required_synthesis_outcome,
                "candidate_outcome": candidate_outcome,
                "allowed_candidate_outcomes": sorted(allowed_candidate_outcomes),
                "restart_selection_outcome": selection_outcome,
                "required_restart_selection_outcome": required_selection_outcome,
                "selected_restart_mode": selected_restart_mode,
                "required_standard_keys": required_standard_keys,
                "standard_keys_complete": standard_keys_complete,
                "transition_levels": transition_levels,
                "transition_levels_required_exact": transition_levels_required_exact,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "formalized_probe_readiness_standard": {
            "comparator_fidelity_minimum": str(candidate_standard.get("comparator_fidelity_minimum", "")).strip(),
            "repeatability_stability_minimum": str(candidate_standard.get("repeatability_stability_minimum", "")).strip(),
            "observable_mapping_minimum": str(candidate_standard.get("observable_mapping_minimum", "")).strip(),
            "numeric_measurement_inputs": str(candidate_standard.get("numeric_measurement_inputs", "")).strip(),
            "partial_hold_routing_rule": str(candidate_standard.get("partial_hold_routing_rule", "")).strip(),
            "transition_levels": transition_levels,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(formalization_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(formalization_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_common_failure_modes_synthesis_report": _ptr(synthesis_path),
            "probe_readiness_standard_candidate_report": _ptr(candidate_path),
            "science_restart_mode_selection_report": _ptr(selection_path),
        },
        "non_claim_boundary": "Repository-local probe-readiness standard formalization report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate probe-readiness standard formalization report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "probe_readiness_standard_formalization_20260412_v0.json",
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
        "probe_readiness_standard_formalization_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
