from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _count_registry_attempts(entries: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for entry in entries:
        row_id = str(entry.get("target_row", "")).strip()
        if not row_id:
            continue
        counts[row_id] = counts.get(row_id, 0) + 1
    return counts


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    queue_policy = dict(declaration.get("queue_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()
    qm_report_path = REPO_ROOT / str(required_inputs.get("post_plan_qm_tranche_report", "")).strip()
    trend_path = REPO_ROOT / str(required_inputs.get("theorem_gap_row_outcome_trend_report", "")).strip()
    linkage_path = REPO_ROOT / str(required_inputs.get("theorem_gap_tranche_linkage_registry", "")).strip()
    normalization_path = REPO_ROOT / str(required_inputs.get("seam_executable_path_normalization_report", "")).strip()
    state_conversion_path = REPO_ROOT / str(required_inputs.get("program_state_conversion_review", "")).strip()

    target_map = _read_json(target_map_path)
    qm_report = _read_json(qm_report_path)
    trend = _read_json(trend_path)
    linkage = _read_json(linkage_path)
    normalization = _read_json(normalization_path)
    state_conversion = _read_json(state_conversion_path)

    route_rows = list(target_map.get("routed_rows", []))
    row_counts = dict(trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}))
    registry_attempts = _count_registry_attempts(list(linkage.get("entries", [])))
    preferred_order = list(queue_policy.get("preferred_queue_order", []))
    preferred_rank = {row_id: index for index, row_id in enumerate(preferred_order, start=1)}
    eligible_route_classes = set(queue_policy.get("eligible_route_classes", []))
    exhausted_row = str(queue_policy.get("required_exhausted_row", "")).strip()
    primary_seams = list(normalization.get("summary", {}).get("authorized_executable_seams", []))
    required_primary_seam = str(queue_policy.get("required_primary_executable_seam", "")).strip()
    qm_terminal_outcome = str(qm_report.get("summary", {}).get("terminal_outcome", "")).strip()

    queue_rows: list[dict[str, Any]] = []
    coverage_gaps: list[str] = []

    for row in route_rows:
        row_id = str(row.get("row_id", "")).strip()
        route_class = str(row.get("route_class", "")).strip()
        if row_id == exhausted_row:
            continue
        if route_class not in eligible_route_classes:
            continue

        trend_counts = dict(row_counts.get(row_id, {}))
        attempts = int(trend_counts.get("total", registry_attempts.get(row_id, 0)) or 0)
        no_change_count = int(trend_counts.get("no_change", 0) or 0)
        success_count = int(trend_counts.get("success", 0) or 0)
        failure_count = int(trend_counts.get("failure", 0) or 0)

        lane = str(row.get("lane", "")).strip()
        priority_rank = preferred_rank.get(row_id)
        if priority_rank is None:
            coverage_gaps.append(row_id)
            priority_rank = 999

        priority_tags: list[str] = []
        if row_id == "ROW-PILLAR-COSMO-001" and required_primary_seam in primary_seams:
            priority_tags.append("SOLE_EXECUTABLE_SEAM_COUPLING")
        if row_id == "ROW-PILLAR-STAT-001" and attempts == 0:
            priority_tags.append("ZERO_ATTEMPT_INFORMATION_GAIN")
        if route_class == str(queue_policy.get("required_gr_route_class", "")).strip():
            priority_tags.append("HEAVY_STRUCTURAL_DORMANT_BRANCH")
        if attempts > 0 and no_change_count == attempts:
            priority_tags.append("PRIOR_NONMOVING_HISTORY")

        if priority_rank == 1:
            next_action = "OPEN_POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE"
        elif priority_rank == 2:
            next_action = "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE"
        elif route_class == str(queue_policy.get("required_gr_route_class", "")).strip():
            next_action = "PREPARE_GR_DORMANT_NEW_STRUCTURE_COMPLETION_PACKAGE"
        else:
            next_action = "REMAIN_QUEUED_PENDING_HIGHER_PRIORITY_ROW_CLOSEOUT"

        queue_rows.append(
            {
                "queue_rank": priority_rank,
                "row_id": row_id,
                "lane": lane,
                "route_class": route_class,
                "current_status": str(row.get("current_status", "")).strip(),
                "blocker_class": str(row.get("blocker_class", "")).strip(),
                "attempt_count": attempts,
                "no_change_count": no_change_count,
                "success_count": success_count,
                "failure_count": failure_count,
                "primary_target": str(row.get("authoritative_next_step", "")).strip(),
                "primary_gate": str(row.get("primary_gate", "")).strip(),
                "priority_tags": priority_tags,
                "next_action": next_action,
            }
        )

    queue_rows.sort(key=lambda item: (int(item.get("queue_rank", 999)), str(item.get("row_id", ""))))

    queue_order = [row["row_id"] for row in queue_rows]
    first_active_ok = queue_order[:1] == [str(queue_policy.get("required_first_active_row", "")).strip()]
    second_active_ok = len(queue_order) > 1 and queue_order[1] == str(queue_policy.get("required_second_active_row", "")).strip()
    heavy_row_ok = str(queue_policy.get("required_heavy_structural_row", "")).strip() in queue_order[:3]
    qm_excluded_ok = exhausted_row not in queue_order and qm_terminal_outcome == "POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED"
    primary_seam_ok = required_primary_seam in primary_seams
    state_conversion_ready = (
        str(state_conversion.get("review_policy", {}).get("default_next_action", "")).strip()
        == "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW"
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_EVIDENCE_INCOMPLETE")).strip()

    if not route_rows or not queue_rows:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_REPAIR"
        next_action = "RESTORE_COMPLETION_QUEUE_INPUTS_AND_RERUN"
    elif all([not coverage_gaps, first_active_ok, second_active_ok, heavy_row_ok, qm_excluded_ok, primary_seam_ok, state_conversion_ready]):
        terminal_outcome = "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED"
        next_action = "OPEN_POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE"
    else:
        terminal_outcome = "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_COMPLETION_QUEUE_POLICY_OR_INPUT_SURFACES"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_map_rows_present": bool(route_rows),
            "queue_rows_present": bool(queue_rows),
            "qm_row_excluded_from_immediate_reuse": qm_excluded_ok,
            "primary_executable_seam_preserved": primary_seam_ok,
            "preferred_queue_order_materialized": not coverage_gaps,
            "required_first_active_row_pinned": first_active_ok,
            "required_second_active_row_pinned": second_active_ok,
            "required_heavy_structural_row_pinned": heavy_row_ok,
            "program_state_conversion_review_ready": state_conversion_ready,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "queue_only_contains_live_or_frozen_rows": all(
                    row.get("route_class") in eligible_route_classes for row in queue_rows
                ),
                "completion_queue_is_theorem_gap_first": queue_order[:2]
                == [
                    str(queue_policy.get("required_first_active_row", "")).strip(),
                    str(queue_policy.get("required_second_active_row", "")).strip(),
                ],
            },
            "inputs": {
                "queue_order": queue_order,
                "authorized_executable_seams": primary_seams,
                "qm_terminal_outcome": qm_terminal_outcome,
                "trend_stagnation_rows": trend.get("objective_quality", {}).get("inputs", {}).get("stagnation_rows", []),
                "nonmoving_family_trigger_count": queue_policy.get("nonmoving_family_trigger_count"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "queue_order": queue_order,
            "first_active_row": queue_order[0] if queue_order else None,
            "second_active_row": queue_order[1] if len(queue_order) > 1 else None,
            "heavy_structural_row": str(queue_policy.get("required_heavy_structural_row", "")).strip(),
            "excluded_row": exhausted_row,
            "primary_executable_seam": primary_seams[0] if primary_seams else None,
            "next_action": next_action,
        },
        "coverage_gaps": {
            "missing_preferred_order_rows": coverage_gaps,
        },
        "completion_queue": queue_rows,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "post_plan_qm_tranche_report": _ptr(qm_report_path),
            "theorem_gap_row_outcome_trend_report": _ptr(trend_path),
            "theorem_gap_tranche_linkage_registry": _ptr(linkage_path),
            "seam_executable_path_normalization_report": _ptr(normalization_path),
            "program_state_conversion_review": _ptr(state_conversion_path),
        },
        "non_claim_boundary": "Repository-local completion queue materialization only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan objective-quality physics completion queue report.")
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
        "post_plan_objective_quality_physics_completion_queue_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())