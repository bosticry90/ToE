from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROBE_READINESS_STANDARD_CANDIDATE_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_CANDIDATE_20260412_v0.json"
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
    candidate_policy = dict(declaration.get("candidate_policy", {}))
    candidate_contract = dict(declaration.get("candidate_contract", {}))

    synthesis_path = REPO_ROOT / str(required_inputs.get("science_common_failure_modes_synthesis_report", "")).strip()
    bridge_policy_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()
    trend_path = REPO_ROOT / str(required_inputs.get("governance_blocker_trend_window_report", "")).strip()

    synthesis = _read_json(synthesis_path)
    bridge_policy = _read_json(bridge_policy_path)
    trend = _read_json(trend_path)

    synthesis_outcome = str(dict(synthesis.get("summary", {})).get("terminal_outcome", "")).strip()
    qm_stat_policy_outcome = str(dict(bridge_policy.get("summary", {})).get("review_outcome", "")).strip()
    trend_status = str(dict(trend.get("trend_summary", {})).get("movement_status", "")).strip()
    trend_net_delta = int(dict(trend.get("blocker_counts", {})).get("net_delta", 0))

    required_synthesis_outcome = str(candidate_policy.get("required_synthesis_outcome", "")).strip()
    required_qm_stat_policy_outcome = str(candidate_policy.get("required_qm_stat_policy_outcome", "")).strip()
    required_trend_status = str(candidate_policy.get("required_trend_movement_status", "")).strip()
    required_trend_net_delta = int(candidate_policy.get("required_trend_net_delta", 0))

    required_standard_keys = list(candidate_contract.get("required_standard_keys", []))
    standard_complete = all(
        key in candidate_policy
        and candidate_policy.get(key) not in ("", None, [])
        for key in required_standard_keys
    )

    preconditions_ok = (
        synthesis_outcome == required_synthesis_outcome
        and qm_stat_policy_outcome == required_qm_stat_policy_outcome
        and trend_status == required_trend_status
        and trend_net_delta == required_trend_net_delta
        and standard_complete
    )

    requires_restart_selection_layer = bool(candidate_policy.get("requires_restart_selection_layer", True))
    architecture_review_required = bool(candidate_policy.get("architecture_review_required", False))

    allowed_outcomes = set(candidate_contract.get("allowed_outcomes", []))
    default_outcome = str(
        candidate_contract.get("default_outcome", "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "PROBE_READINESS_STANDARD_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_REQUIRED_INPUTS_AND_RERUN_STANDARD_CANDIDATE_LAYER"
    elif architecture_review_required:
        terminal_outcome = "HOLD_PENDING_ARCHITECTURE_REVIEW"
        next_action = "OPEN_ONE_BOUNDED_ARCHITECTURE_REVIEW_LAYER"
    elif requires_restart_selection_layer:
        terminal_outcome = "REQUIRES_RESTART_SELECTION_LAYER"
        next_action = "OPEN_ONE_BOUNDED_RESTART_SELECTION_LAYER"
    else:
        terminal_outcome = "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED"
        next_action = "REGISTER_STANDARD_CANDIDATE_AND_WAIT_FOR_AUTHORIZATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "synthesis_outcome_match": synthesis_outcome == required_synthesis_outcome,
            "qm_stat_policy_outcome_match": qm_stat_policy_outcome == required_qm_stat_policy_outcome,
            "trend_plateau_match": trend_status == required_trend_status and trend_net_delta == required_trend_net_delta,
            "standard_keys_complete": standard_complete,
            "single_terminal_outcome_rule_declared": str(
                candidate_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_PROBE_READINESS_STANDARD_CANDIDATE_OUTCOME",
            "no_loop_rule_declared": str(candidate_contract.get("no_loop_rule", "")).strip()
            == "ONE_PROBE_READINESS_STANDARD_CANDIDATE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "candidate_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "synthesis_outcome": synthesis_outcome,
                "required_synthesis_outcome": required_synthesis_outcome,
                "qm_stat_policy_outcome": qm_stat_policy_outcome,
                "required_qm_stat_policy_outcome": required_qm_stat_policy_outcome,
                "trend_movement_status": trend_status,
                "required_trend_movement_status": required_trend_status,
                "trend_net_delta": trend_net_delta,
                "required_trend_net_delta": required_trend_net_delta,
                "required_standard_keys": required_standard_keys,
                "standard_keys_complete": standard_complete,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "probe_readiness_standard_candidate": {
            "comparator_fidelity_minimum": str(candidate_policy.get("comparator_fidelity_minimum", "")).strip(),
            "repeatability_stability_minimum": str(candidate_policy.get("repeatability_stability_minimum", "")).strip(),
            "observable_mapping_minimum": str(candidate_policy.get("observable_mapping_minimum", "")).strip(),
            "numeric_measurement_inputs": str(candidate_policy.get("numeric_measurement_inputs", "")).strip(),
            "partial_hold_routing_rule": str(candidate_policy.get("partial_hold_routing_rule", "")).strip(),
            "transition_levels": list(candidate_policy.get("transition_levels", [])),
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(candidate_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(candidate_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_common_failure_modes_synthesis_report": _ptr(synthesis_path),
            "bridge_external_validation_policy_review_report": _ptr(bridge_policy_path),
            "governance_blocker_trend_window_report": _ptr(trend_path),
        },
        "non_claim_boundary": "Repository-local probe-readiness standard candidate report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate probe-readiness standard candidate report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "probe_readiness_standard_candidate_20260412_v0.json",
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
        "probe_readiness_standard_candidate_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
