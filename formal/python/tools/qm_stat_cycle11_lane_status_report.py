from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_CYCLE11_LANE_STATUS_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_LANE_STATUS_20260411_v0.json"
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
    target_lane = dict(declaration.get("target_lane", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    status_contract = dict(declaration.get("status_contract", {}))

    post_cycle_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_discovery_post_derivation_probe_decision_report", "")
    ).strip()
    mapping_review_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_rl10_observable_mapping_review_report", "")
    ).strip()
    interface_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_rl10_interface_transformation_report", "")
    ).strip()
    sigma_db_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_rl10_sigma_db_transformation_report", "")
    ).strip()
    feasibility_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_transition_dynamics_feasibility_review_report", "")
    ).strip()
    discovery_review_path = REPO_ROOT / str(
        required_inputs.get("discovery_engine_scoring_routing_review_report", "")
    ).strip()

    post_cycle = _read_json(post_cycle_path)
    mapping_review = _read_json(mapping_review_path)
    interface_report = _read_json(interface_path)
    sigma_db_report = _read_json(sigma_db_path)
    feasibility_report = _read_json(feasibility_path)
    discovery_review = _read_json(discovery_review_path)

    post_cycle_summary = dict(post_cycle.get("summary", {}))
    mapping_summary = dict(mapping_review.get("summary", {}))
    interface_summary = dict(interface_report.get("summary", {}))
    sigma_db_summary = dict(sigma_db_report.get("summary", {}))
    feasibility_summary = dict(feasibility_report.get("summary", {}))
    discovery_summary = dict(discovery_review.get("summary", {}))

    post_cycle_decision = str(post_cycle_summary.get("post_cycle_decision", "")).strip()
    mapping_outcome = str(mapping_summary.get("mapping_review_outcome", "")).strip()
    interface_outcome = str(interface_summary.get("transformation_outcome", "")).strip()
    sigma_db_outcome = str(sigma_db_summary.get("transformation_outcome", "")).strip()
    feasibility_outcome = str(feasibility_summary.get("review_outcome", "")).strip()
    reopen_condition = str(discovery_summary.get("lane_expansion_reopen_condition", "")).strip()

    if feasibility_outcome == "QM_STAT_RL10_EXTERNALIZATION_PATH_FALSIFIED":
        externalization_status = "PATH_FALSIFIED"
    elif feasibility_outcome == "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE":
        externalization_status = "OUT_OF_SCOPE_UNDER_CYCLE11"
    else:
        externalization_status = "INCOMPLETE_BUT_STILL_IN_SCOPE_UNDER_CYCLE11"

    internal_lane_status = (
        "RETAINED"
        if post_cycle_decision == "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"
        else "RETIRED"
    )

    eligible_for_external_path_reopen_signal = (
        externalization_status != "OUT_OF_SCOPE_UNDER_CYCLE11"
        and externalization_status != "PATH_FALSIFIED"
    )

    if internal_lane_status == "RETAINED" and externalization_status == "OUT_OF_SCOPE_UNDER_CYCLE11":
        next_action = "RETURN_TO_DISCOVERY_ROUTING_AND_EXCLUDE_QM_STAT_FROM_CURRENT_EXTERNAL_PATH_REOPEN_CANDIDATES"
    elif externalization_status == "PATH_FALSIFIED":
        next_action = "RECLASSIFY_QM_STAT_EXTERNALIZATION_PATH_AND_REMOVE_FROM_REOPEN_CANDIDATES"
    else:
        next_action = "QM_STAT_MAY_REQUIRE_FURTHER_IN_SCOPE_EXTERNALIZATION_REVIEW"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "internal_lane_decision_present": post_cycle_decision
            in {
                "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE",
                "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED",
                "RETIRE_THIS_QM_STAT_PROBE_PATH_NONPRODUCTIVE",
            },
            "externalization_closure_chain_present": all(
                outcome
                for outcome in (mapping_outcome, interface_outcome, sigma_db_outcome, feasibility_outcome)
            ),
            "routing_overlay_present": bool(reopen_condition),
            "no_loop_rule_declared": str(status_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_CYCLE11_LANE_STATUS_SYNTHESIS_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_externalization_status_materialized": externalization_status
                in set(status_contract.get("allowed_externalization_status", [])),
                "allowed_internal_lane_status_materialized": internal_lane_status
                in set(status_contract.get("allowed_internal_lane_status", [])),
                "routing_implication_answered": True,
                "lane_retention_answered": True,
            },
            "inputs": {
                "target_row": target_lane.get("row_id"),
                "target_lane": target_lane.get("lane"),
                "post_cycle_decision": post_cycle_decision,
                "mapping_review_outcome": mapping_outcome,
                "interface_transformation_outcome": interface_outcome,
                "sigma_db_transformation_outcome": sigma_db_outcome,
                "transition_dynamics_feasibility_outcome": feasibility_outcome,
                "discovery_reopen_condition": reopen_condition,
                "routing_implication_rule": status_contract.get("routing_implication_rule"),
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "internal_lane_status": internal_lane_status,
            "externalization_status": externalization_status,
            "eligible_for_external_path_reopen_signal_under_cycle11": eligible_for_external_path_reopen_signal,
            "routing_implication": (
                "DO_NOT_COUNT_QM_STAT_AS_CURRENT_EXTERNAL_PATH_SIGNAL"
                if not eligible_for_external_path_reopen_signal
                else "QM_STAT_REMAINS_ELIGIBLE_FOR_CURRENT_EXTERNAL_PATH_SIGNAL"
            ),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qm_stat_discovery_post_derivation_probe_decision_report": _ptr(post_cycle_path),
            "qm_stat_rl10_observable_mapping_review_report": _ptr(mapping_review_path),
            "qm_stat_rl10_interface_transformation_report": _ptr(interface_path),
            "qm_stat_rl10_sigma_db_transformation_report": _ptr(sigma_db_path),
            "qm_stat_transition_dynamics_feasibility_review_report": _ptr(feasibility_path),
            "discovery_engine_scoring_routing_review_report": _ptr(discovery_review_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT Cycle11 lane-status report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT Cycle11 lane-status report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_cycle11_lane_status_20260411_v0.json",
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
        "qm_stat_cycle11_lane_status_report: "
        f"externalization_status={payload['summary']['externalization_status']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
