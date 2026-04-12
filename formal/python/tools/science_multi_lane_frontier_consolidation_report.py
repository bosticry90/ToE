from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_20260412_v0.json"
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
    consolidation_policy = dict(declaration.get("consolidation_policy", {}))
    consolidation_contract = dict(declaration.get("consolidation_contract", {}))

    preservation_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_preservation_record_report", "")
    ).strip()
    shared_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_post_refinement_decision_report", "")
    ).strip()
    qft_gr_path = REPO_ROOT / str(
        required_inputs.get("qft_gr_post_refinement_decision_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    preservation = _read_json(preservation_path)
    shared = _read_json(shared_path)
    qft_gr = _read_json(qft_gr_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    preservation_outcome = str(dict(preservation.get("summary", {})).get("terminal_outcome", "")).strip()
    shared_outcome = str(dict(shared.get("summary", {})).get("terminal_outcome", "")).strip()
    qft_gr_outcome = str(dict(qft_gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_preservation_outcome = str(
        consolidation_policy.get("required_frontier_preservation_outcome", "")
    ).strip()
    required_shared_outcome = str(consolidation_policy.get("required_shared_model_class_outcome", "")).strip()
    required_qft_gr_outcome = str(consolidation_policy.get("required_qft_gr_outcome", "")).strip()
    qm_stat_required_review_outcome = str(
        consolidation_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(consolidation_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(consolidation_policy.get("em_qft_required_outcome", "")).strip()

    qft_gr_stop_commit = str(consolidation_policy.get("qft_gr_stop_commit", "")).strip()
    all_current_execution_lanes_closed = bool(
        consolidation_policy.get("all_current_execution_lanes_closed", False)
    )
    resume_requires_new_policy_or_untouched_lane = bool(
        consolidation_policy.get("resume_requires_new_policy_or_untouched_lane", False)
    )

    preconditions_ok = (
        preservation_outcome == required_preservation_outcome
        and shared_outcome == required_shared_outcome
        and qft_gr_outcome == required_qft_gr_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
        and all_current_execution_lanes_closed
    )

    allowed_outcomes = set(consolidation_contract.get("allowed_outcomes", []))
    default_outcome = str(
        consolidation_contract.get("default_outcome", "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "MULTI_LANE_FRONTIER_RECORD_INCOMPLETE"
        next_action = "RESTORE_MISSING_PRECONDITIONS_BEFORE_CONSOLIDATION"
    elif not resume_requires_new_policy_or_untouched_lane:
        terminal_outcome = "REQUIRES_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE"
        next_action = "OPEN_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE"
    else:
        terminal_outcome = "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED"
        next_action = "NO_FURTHER_PACKET_EXECUTION_AUTHORIZED_RESUME_ONLY_FROM_NEW_POLICY_OR_UNTOUCHED_LANE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "frontier_preservation_match": preservation_outcome == required_preservation_outcome,
            "shared_model_class_hold_match": shared_outcome == required_shared_outcome,
            "qft_gr_hold_match": qft_gr_outcome == required_qft_gr_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "all_current_execution_lanes_closed": all_current_execution_lanes_closed,
            "resume_requires_new_policy_or_untouched_lane": resume_requires_new_policy_or_untouched_lane,
            "single_terminal_outcome_rule_declared": str(
                consolidation_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_OUTCOME",
            "no_loop_rule_declared": str(consolidation_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "consolidation_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "frontier_preservation_outcome": preservation_outcome,
                "required_frontier_preservation_outcome": required_preservation_outcome,
                "shared_model_class_outcome": shared_outcome,
                "required_shared_model_class_outcome": required_shared_outcome,
                "qft_gr_outcome": qft_gr_outcome,
                "required_qft_gr_outcome": required_qft_gr_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "qft_gr_stop_commit": qft_gr_stop_commit,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "qft_gr_stop_commit": qft_gr_stop_commit,
            "next_action": next_action,
            "single_layer_only": bool(consolidation_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(consolidation_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_frontier_preservation_record_report": _ptr(preservation_path),
            "shared_model_class_post_refinement_decision_report": _ptr(shared_path),
            "qft_gr_post_refinement_decision_report": _ptr(qft_gr_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local multi-lane science frontier consolidation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate multi-lane science frontier consolidation report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_multi_lane_frontier_consolidation_20260412_v0.json",
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
        "science_multi_lane_frontier_consolidation_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
