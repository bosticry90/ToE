from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_20260411_v0.json"
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
    target_seam = dict(declaration.get("target_seam", {}))
    baseline_comparator = dict(declaration.get("baseline_comparator", {}))
    candidate_signal = dict(declaration.get("candidate_external_path_signal", {}))
    execution_contract = dict(declaration.get("execution_contract", {}))
    selection_policy = dict(declaration.get("selection_policy", {}))

    scoring_review_path = REPO_ROOT / str(required_inputs.get("discovery_engine_scoring_routing_review_report", "")).strip()
    checkpoint_path = REPO_ROOT / str(required_inputs.get("discovery_engine_review_checkpoint_report", "")).strip()
    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()
    interpretation_path = REPO_ROOT / str(required_inputs.get("qm_stat_discovery_interpretation_report", "")).strip()
    probe_execution_path = REPO_ROOT / str(required_inputs.get("qm_stat_discovery_numerical_probe_execution_report", "")).strip()
    post_cycle_path = REPO_ROOT / str(required_inputs.get("qm_stat_discovery_post_derivation_probe_decision_report", "")).strip()

    scoring_review = _read_json(scoring_review_path)
    checkpoint = _read_json(checkpoint_path)
    queue = _read_json(queue_path)
    comparator = _read_json(comparator_path)
    interpretation = _read_json(interpretation_path)
    probe_execution = _read_json(probe_execution_path)
    post_cycle = _read_json(post_cycle_path)

    scoring_summary = dict(scoring_review.get("summary", {}))
    checkpoint_summary = dict(checkpoint.get("summary", {}))
    queue_summary = dict(queue.get("summary", {}))
    comparator_summary = dict(comparator.get("summary", {}))
    interpretation_summary = dict(interpretation.get("summary", {}))
    probe_summary = dict(probe_execution.get("summary", {}))
    post_cycle_summary = dict(post_cycle.get("summary", {}))

    target_row = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()
    top_rank_row = str(queue_summary.get("top_rank_row", "")).strip()
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()
    interpretation_value = str(interpretation_summary.get("interpretation", "")).strip()
    probe_signal = str(probe_summary.get("probe_signal", "")).strip()
    post_cycle_decision = str(post_cycle_summary.get("post_cycle_decision", "")).strip()
    credible_external_path_signal_present = bool(scoring_summary.get("credible_external_path_signal_present", False))
    hold_active = (
        str(scoring_summary.get("selected_review_disposition", "")).strip()
        == "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY"
        and str(checkpoint_summary.get("selected_expansion_decision", "")).strip()
        == "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT"
    )

    target_is_top_ranked = target_row != "" and target_row == top_rank_row
    target_alignment = target_row == str(interpretation_summary.get("target_row", target_row)).strip()
    baseline_comparator_declared = comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
    internal_only_state = (
        interpretation_value == "INTERNAL_DISCRIMINATIVE_ONLY"
        and probe_signal in {"PROBE_NONDISCRIMINATIVE", "PROBE_NOT_EXECUTED"}
        and post_cycle_decision == "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"
    )

    if credible_external_path_signal_present:
        packet_outcome = "QM_STAT_EXTERNAL_PATH_SIGNAL_ALREADY_PRESENT"
        next_action = "REOPEN_DISCOVERY_EXPANSION_REVIEW_ONCE"
    elif hold_active and target_is_top_ranked and target_alignment and internal_only_state and baseline_comparator_declared:
        packet_outcome = "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED"
        next_action = "EXECUTE_ONE_QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_ONCE"
    else:
        packet_outcome = "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_INCOMPLETE"
        next_action = "REPAIR_QM_STAT_EXTERNALIZATION_INPUTS_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "hold_state_active": hold_active,
            "target_row_remains_top_ranked": target_is_top_ranked,
            "target_alignment_present": target_alignment,
            "credible_external_path_signal_absent": not credible_external_path_signal_present,
            "single_baseline_comparator_declared": baseline_comparator_declared,
            "bounded_packet_materialized": packet_outcome
            in {
                "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED",
                "QM_STAT_EXTERNAL_PATH_SIGNAL_ALREADY_PRESENT",
            },
        },
        "objective_quality": {
            "criteria": {
                "baseline_comparator_declared": baseline_comparator_declared,
                "candidate_signal_declared": bool(str(candidate_signal.get("signal_id", "")).strip()),
                "one_shot_contract_declared": str(execution_contract.get("no_loop_rule", "")).strip()
                == "ONE_EXTERNAL_PATH_SIGNAL_PACKET_ONLY",
                "review_gating_respected": not credible_external_path_signal_present or packet_outcome
                == "QM_STAT_EXTERNAL_PATH_SIGNAL_ALREADY_PRESENT",
            },
            "inputs": {
                "target_row": target_row,
                "target_lane": target_lane,
                "top_rank_row": top_rank_row,
                "current_interpretation": interpretation_value,
                "current_probe_signal": probe_signal,
                "current_post_cycle_decision": post_cycle_decision,
                "baseline_comparator": baseline_comparator,
                "baseline_comparator_report_status": comparator_status,
                "candidate_external_path_signal": candidate_signal,
                "allowed_outcomes": execution_contract.get("allowed_outcomes", []),
                "success_rule": execution_contract.get("success_rule"),
                "failure_rule": execution_contract.get("failure_rule"),
                "path_falsification_rule": execution_contract.get("path_falsification_rule"),
                "no_loop_rule": execution_contract.get("no_loop_rule"),
                "selected_review_disposition": scoring_summary.get("selected_review_disposition"),
                "checkpoint_selected_expansion_decision": checkpoint_summary.get("selected_expansion_decision"),
                "credible_external_path_signal_present": credible_external_path_signal_present,
            },
            "summary": {
                "all_criteria_satisfied": packet_outcome
                in {
                    "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED",
                    "QM_STAT_EXTERNAL_PATH_SIGNAL_ALREADY_PRESENT",
                },
                "phase_status": "COMPLETE"
                if packet_outcome
                in {
                    "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED",
                    "QM_STAT_EXTERNAL_PATH_SIGNAL_ALREADY_PRESENT",
                }
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "selected_target_row": target_row,
            "selected_target_lane": target_lane,
            "baseline_comparator_id": baseline_comparator.get("comparator_id"),
            "baseline_comparator_status": comparator_status,
            "candidate_external_path_signal_id": candidate_signal.get("signal_id"),
            "candidate_external_path_signal_definition": candidate_signal.get("signal_definition"),
            "allowed_outcomes": execution_contract.get("allowed_outcomes", []),
            "success_rule": execution_contract.get("success_rule"),
            "failure_rule": execution_contract.get("failure_rule"),
            "no_loop_rule": execution_contract.get("no_loop_rule"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_engine_scoring_routing_review_report": _ptr(scoring_review_path),
            "discovery_engine_review_checkpoint_report": _ptr(checkpoint_path),
            "discovery_priority_queue_report": _ptr(queue_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
            "qm_stat_discovery_interpretation_report": _ptr(interpretation_path),
            "qm_stat_discovery_numerical_probe_execution_report": _ptr(probe_execution_path),
            "qm_stat_discovery_post_derivation_probe_decision_report": _ptr(post_cycle_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT external-path signal packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT external-path signal packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_external_path_signal_packet_20260411_v0.json",
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
        "qm_stat_external_path_signal_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
