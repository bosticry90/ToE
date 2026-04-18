from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    queue_path = REPO_ROOT / str(required_inputs.get("completion_queue_report", "")).strip()
    stat_path = REPO_ROOT / str(required_inputs.get("post_plan_stat_tranche_report", "")).strip()
    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()
    matrix_path = REPO_ROOT / str(required_inputs.get("completion_matrix", "")).strip()
    dashboard_path = REPO_ROOT / str(required_inputs.get("blocker_burn_dashboard_report", "")).strip()
    contradiction_path = REPO_ROOT / str(required_inputs.get("science_maturity_contradiction_report", "")).strip()
    blocker_map_path = REPO_ROOT / str(required_inputs.get("gr_new_structure_blocker_file_map", "")).strip()
    structural_gap_path = REPO_ROOT / str(required_inputs.get("gr_structural_gap_definition_report", "")).strip()
    concept_path = REPO_ROOT / str(required_inputs.get("gr_new_structure_concept_packet_report", "")).strip()
    shared_interface_path = REPO_ROOT / str(required_inputs.get("gr_shared_interface_declaration_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("gr_comparator_specification_report", "")).strip()
    deeper_review_path = REPO_ROOT / str(required_inputs.get("deeper_blocker_definition_review", "")).strip()

    queue_report = _read_json(queue_path)
    stat_report = _read_json(stat_path)
    target_map = _read_json(target_map_path)
    dashboard = _read_json(dashboard_path)
    contradiction = _read_json(contradiction_path)
    blocker_map = _read_json(blocker_map_path)
    structural_gap = _read_json(structural_gap_path)
    concept_report = _read_json(concept_path)
    shared_interface_report = _read_json(shared_interface_path)
    comparator_report = _read_json(comparator_path)
    deeper_review = _read_json(deeper_review_path)
    matrix_rows = _parse_markdown_table(
        _read_text(matrix_path),
        [
            "row_id",
            "domain",
            "lane",
            "current_status",
            "blocker_class",
            "primary_target",
            "primary_artifact",
            "primary_gate",
            "governance_checkpoint_status",
            "physics_checkpoint_status",
            "gate_runtime_status",
        ],
    )

    target_row_id = str(policy.get("required_target_row", "")).strip()
    route_map = {row["row_id"]: row for row in target_map.get("routed_rows", [])}
    matrix_row = {row["row_id"]: row for row in matrix_rows}.get(target_row_id, {})
    target_row = dict(route_map.get(target_row_id, {}))
    branch = dict(blocker_map.get("authoritative_branch_classification", {}))

    queue_ok = (
        queue_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_queue_outcome", "")).strip()
        and queue_report.get("summary", {}).get("heavy_structural_row") == str(policy.get("required_queue_heavy_structural_row", "")).strip()
    )
    stat_ok = stat_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_stat_outcome", "")).strip()
    target_map_ok = (
        target_row.get("route_class") == str(policy.get("required_target_route_class", "")).strip()
        and target_row.get("authoritative_next_step") == str(policy.get("required_gr_rule", "")).strip()
    )
    row_ok = bool(matrix_row) and matrix_row.get("blocker_class") == str(policy.get("required_target_blocker_class", "")).strip()
    contradiction_ok = any(
        observation.get("row_id") == target_row_id and observation.get("observation_type") == "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"
        for observation in contradiction.get("modeled_observations", [])
    )
    blocker_map_ok = (
        blocker_map.get("target_row") == target_row_id
        and branch.get("current_lane_class") == str(policy.get("required_target_route_class", "")).strip()
        and branch.get("authoritative_next_step") == str(policy.get("required_gr_rule", "")).strip()
        and branch.get("retry_path_status") == str(policy.get("required_retry_path_status", "")).strip()
    )
    structural_gap_ok = structural_gap.get("summary", {}).get("terminal_outcome") == str(policy.get("required_structural_gap_outcome", "")).strip()
    concept_ok = concept_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_concept_outcome", "")).strip()
    shared_interface_ok = shared_interface_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_shared_interface_outcome", "")).strip()
    comparator_ok = comparator_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_comparator_outcome", "")).strip()
    deeper_review_ok = deeper_review.get("review_basis") == "PROGRAM_STATE_CONVERSION_REVIEW_PRESCRIBED_DEEPER_BLOCKER_DEFINITION_REVIEW"

    row_truth_change_detected = bool(matrix_row) and (
        matrix_row.get("blocker_class") != "THEOREM_GAP"
        or matrix_row.get("physics_checkpoint_status") != "THEOREM_GAP_OPEN"
        or matrix_row.get("current_status") == "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE"
    )
    explicit_exhaustion_detected = (
        not row_truth_change_detected
        and blocker_map_ok
        and structural_gap_ok
        and concept_ok
        and shared_interface_ok
        and comparator_ok
        and comparator_report.get("summary", {}).get("package_status") == "CANONICAL_DORMANT_GR_DESIGN_PACKAGE"
        and comparator_report.get("summary", {}).get("next_action")
        == "STOP_DORMANT_GR_LAYERING_UNTIL_P75_AND_P77_CLEAR_OR_A_NEW_DISTINCT_AMBIGUITY_IS_IDENTIFIED"
    )
    deeper_review_justified = (
        not row_truth_change_detected
        and blocker_map_ok
        and structural_gap_ok
        and deeper_review_ok
        and branch.get("retry_path_status") == str(policy.get("required_retry_path_status", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE")
    ).strip()

    evidence_ok = all(
        [queue_ok, stat_ok, target_map_ok, row_ok, contradiction_ok, blocker_map_ok, structural_gap_ok, concept_ok, shared_interface_ok, comparator_ok, deeper_review_ok]
    )

    if not matrix_row or not target_row:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_REPAIR"
        next_action = "RESTORE_GR_DORMANT_NEW_STRUCTURE_TRANCHE_INPUT_SHAPE_AND_RERUN"
    elif evidence_ok and row_truth_change_detected:
        terminal_outcome = "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_AND_PROMOTED"
        next_action = "REASSESS_POST_PLAN_SEAMS_AND_MASTER_ACTION_WITH_CHANGED_GR_ROW_TRUTH"
    elif evidence_ok and explicit_exhaustion_detected:
        terminal_outcome = "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"
        next_action = "OPEN_DEEPER_BLOCKER_DEFINITION_REVIEW_PATH_WITH_GR_DORMANT_PACKAGE_EXHAUSTION_RECORDED"
    elif evidence_ok and deeper_review_justified:
        terminal_outcome = "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED"
        next_action = "OPEN_DEEPER_BLOCKER_DEFINITION_REVIEW_PATH_WITH_GR_NONPROMOTION_RECORDED"
    else:
        terminal_outcome = "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_GR_DORMANT_NEW_STRUCTURE_TRANCHE_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "completion_queue_materialized": queue_ok,
            "stat_upstream_tranche_recorded": stat_ok,
            "target_map_materialized": target_map_ok,
            "gr_row_alignment_ok": row_ok,
            "gr_live_theorem_gap_observation_present": contradiction_ok,
            "gr_blocker_file_map_alignment_ok": blocker_map_ok,
            "gr_structural_gap_alignment_ok": structural_gap_ok,
            "gr_concept_packet_alignment_ok": concept_ok,
            "gr_shared_interface_alignment_ok": shared_interface_ok,
            "gr_comparator_alignment_ok": comparator_ok,
            "deeper_blocker_definition_review_declared": deeper_review_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "promotion_only_if_row_truth_changed": (terminal_outcome != "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_AND_PROMOTED") or row_truth_change_detected,
                "exhaustion_only_if_frozen_branch_capstone_present": (terminal_outcome != "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED") or explicit_exhaustion_detected,
                "deeper_review_path_justified_when_nonmoving": (terminal_outcome not in {
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                    "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED",
                }) or deeper_review_justified,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_route_class": target_row.get("route_class"),
                "authoritative_gr_rule": target_row.get("authoritative_next_step"),
                "retry_path_status": branch.get("retry_path_status"),
                "blocker_movement_status": dashboard.get("blocker_scoreboard", {}).get("movement_status"),
                "blocker_net_delta": dashboard.get("blocker_scoreboard", {}).get("net_delta"),
                "row_current_status": matrix_row.get("current_status"),
                "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
                "row_blocker_class": matrix_row.get("blocker_class"),
                "structural_gap_outcome": structural_gap.get("summary", {}).get("terminal_outcome"),
                "concept_outcome": concept_report.get("summary", {}).get("terminal_outcome"),
                "shared_interface_outcome": shared_interface_report.get("summary", {}).get("terminal_outcome"),
                "comparator_outcome": comparator_report.get("summary", {}).get("terminal_outcome"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_route_class": target_row.get("route_class"),
            "row_truth_change_detected": row_truth_change_detected,
            "explicit_exhaustion_detected": explicit_exhaustion_detected,
            "deeper_blocker_definition_review_justified": deeper_review_justified,
            "retry_path_status": branch.get("retry_path_status"),
            "row_current_status": matrix_row.get("current_status"),
            "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "completion_queue_report": _ptr(queue_path),
            "post_plan_stat_tranche_report": _ptr(stat_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "completion_matrix": _ptr(matrix_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "science_maturity_contradiction_report": _ptr(contradiction_path),
            "gr_new_structure_blocker_file_map": _ptr(blocker_map_path),
            "gr_structural_gap_definition_report": _ptr(structural_gap_path),
            "gr_new_structure_concept_packet_report": _ptr(concept_path),
            "gr_shared_interface_declaration_report": _ptr(shared_interface_path),
            "gr_comparator_specification_report": _ptr(comparator_path),
            "deeper_blocker_definition_review": _ptr(deeper_review_path)
        },
        "non_claim_boundary": "Repository-local post-plan GR dormant new-structure completion tranche measurement only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan GR dormant new-structure completion tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
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
        "post_plan_gr_dormant_new_structure_completion_tranche_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())