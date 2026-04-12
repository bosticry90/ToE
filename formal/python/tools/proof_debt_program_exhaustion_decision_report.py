from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_PROGRAM_EXHAUSTION_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_PROGRAM_EXHAUSTION_DECISION_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_many(root: Path, raw: Any) -> tuple[list[Path], list[dict[str, Any]]]:
    if isinstance(raw, str):
        relpaths = [raw] if raw.strip() else []
    elif isinstance(raw, list):
        relpaths = [str(item) for item in raw if str(item).strip()]
    else:
        relpaths = []

    paths = [root / relpath for relpath in relpaths]
    payloads = [_read_json(path) for path in paths]
    return paths, payloads


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _movement_flags(surface_ruling: dict[str, Any]) -> dict[str, bool]:
    inputs = dict(surface_ruling.get("objective_quality", {}).get("inputs", {}))
    movement = dict(inputs.get("movement_signals", {}))
    return {
        "theorem_gap_state_changed": bool(movement.get("theorem_gap_state_changed", False)),
        "seam_integration_state_changed": bool(movement.get("seam_integration_state_changed", False)),
        "global_row_success_state_changed": bool(movement.get("global_row_success_state_changed", False)),
        "blocker_state_token_changed": bool(movement.get("blocker_state_token_changed", False)),
    }


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))

    current_attack_class_decision_path = REPO_ROOT / str(required_inputs.get("current_attack_class_decision_report", ""))
    next_cluster_selection_path = REPO_ROOT / str(required_inputs.get("next_cluster_selection_report", ""))
    cluster_focus_paths, cluster_focus_reports = _read_many(REPO_ROOT, required_inputs.get("cluster_focus_reports", []))
    surface_ruling_paths, surface_ruling_reports = _read_many(REPO_ROOT, required_inputs.get("surface_ruling_reports", []))

    current_attack_class_decision = _read_json(current_attack_class_decision_path)
    next_cluster_selection = _read_json(next_cluster_selection_path)

    current_attack_class = str(declaration.get("current_attack_class", "")).strip()
    upstream_attack_class = str(
        current_attack_class_decision.get("summary", {}).get("selected_next_experimental_class", "")
    ).strip()

    cluster_focus_summaries = []
    for payload in cluster_focus_reports:
        cluster_focus_summaries.append(
            {
                "cluster_id": payload.get("cluster_id"),
                "selection_outcome": payload.get("summary", {}).get("selection_outcome"),
                "excluded_surface_ids": payload.get("summary", {}).get("excluded_surface_ids", []),
            }
        )

    all_cluster_focus_reports_exhausted = bool(cluster_focus_summaries) and all(
        row.get("selection_outcome") == "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE" for row in cluster_focus_summaries
    )

    tested_surface_summaries = []
    any_theorem_gap_change = False
    any_seam_change = False
    any_global_row_change = False
    any_blocker_token_change = False
    any_blocker_movement = False

    for payload in surface_ruling_reports:
        summary = dict(payload.get("summary", {}))
        movement_flags = _movement_flags(payload)
        any_theorem_gap_change = any_theorem_gap_change or movement_flags["theorem_gap_state_changed"]
        any_seam_change = any_seam_change or movement_flags["seam_integration_state_changed"]
        any_global_row_change = any_global_row_change or movement_flags["global_row_success_state_changed"]
        any_blocker_token_change = any_blocker_token_change or movement_flags["blocker_state_token_changed"]
        any_blocker_movement = any_blocker_movement or bool(summary.get("blocker_facing_movement_observed", False))

        tested_surface_summaries.append(
            {
                "cluster_id": payload.get("cluster_id"),
                "surface_id": summary.get("surface_id"),
                "surface_ruling": summary.get("surface_ruling"),
                "gate_passed": bool(summary.get("gate_passed", False)),
                "exclude_from_immediate_reselection": bool(summary.get("exclude_from_immediate_reselection", False)),
                "blocker_facing_movement_observed": bool(summary.get("blocker_facing_movement_observed", False)),
                "movement_signals": movement_flags,
            }
        )

    exhausted_cluster_ids = list(
        next_cluster_selection.get("summary", {}).get("exhausted_from_active_surface_selector", [])
    )
    next_cluster_selection_outcome = str(next_cluster_selection.get("summary", {}).get("selection_outcome", ""))
    no_eligible_cluster_remains = next_cluster_selection_outcome == "NO_ELIGIBLE_CLUSTER_UNDER_CURRENT_FILTER"

    specific_filter_defect_identified = bool(decision_policy.get("specific_filter_defect_identified", False))
    specific_filter_defect_note = decision_policy.get("specific_filter_defect_note")
    bounded_filter_revision_packet = decision_policy.get("bounded_filter_revision_packet")
    bounded_filter_revision_defined = isinstance(bounded_filter_revision_packet, str) and bool(
        bounded_filter_revision_packet.strip()
    )
    next_attack_class_if_escalated = str(decision_policy.get("next_attack_class_if_escalated", "")).strip() or None
    surface_run_hold_policy = str(decision_policy.get("surface_run_hold_policy", "")).strip()

    no_tested_surface_movement = not any(
        [
            any_theorem_gap_change,
            any_seam_change,
            any_global_row_change,
            any_blocker_token_change,
            any_blocker_movement,
        ]
    )

    all_eligible_current_clusters_exhausted = no_eligible_cluster_remains and all_cluster_focus_reports_exhausted

    if specific_filter_defect_identified and bounded_filter_revision_defined:
        program_state = "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
        filter_revision_status = "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
        decision = "EXECUTE_FILTER_REVISION_PACKET_ONCE"
        next_action = "EXECUTE_FILTER_REVISION_PACKET_ONCE"
        selected_next_attack_class = None
    elif all_eligible_current_clusters_exhausted and no_tested_surface_movement:
        program_state = "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
        filter_revision_status = "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED"
        decision = "ESCALATE_TO_NEXT_ATTACK_CLASS"
        if next_attack_class_if_escalated and next_attack_class_if_escalated != "NEW_ATTACK_CLASS_REQUIRED":
            next_action = f"EXECUTE_{next_attack_class_if_escalated}_BOUNDED_PACKET"
            selected_next_attack_class = next_attack_class_if_escalated
        else:
            next_action = "MATERIALIZE_ONE_NEW_ATTACK_CLASS_PACKET"
            selected_next_attack_class = None
    else:
        program_state = "PROOF_DEBT_PROGRAM_NOT_YET_EXHAUSTED_OR_INPUTS_INCOMPLETE"
        filter_revision_status = (
            "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
            if specific_filter_defect_identified and bounded_filter_revision_defined
            else "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED"
        )
        decision = "REPAIR_DECISION_INPUTS_OR_REVIEW_EXHAUSTION_STATE"
        next_action = "REVIEW_INPUT_STATE_AND_DO_NOT_RUN_ADDITIONAL_SURFACES_YET"
        selected_next_attack_class = None

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "current_attack_class": current_attack_class,
        "criteria": {
            "current_attack_class_matches_upstream_decision": current_attack_class != "" and current_attack_class == upstream_attack_class,
            "all_eligible_current_clusters_exhausted_under_current_filter": all_eligible_current_clusters_exhausted,
            "no_tested_surface_theorem_gap_change_observed": not any_theorem_gap_change,
            "no_tested_surface_seam_integration_change_observed": not any_seam_change,
            "no_tested_surface_global_row_success_change_observed": not any_global_row_change,
            "no_tested_surface_blocker_token_change_observed": not any_blocker_token_change,
            "specific_filter_defect_identified": specific_filter_defect_identified,
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "no_further_surface_runs_enforced": (
                    surface_run_hold_policy == "NO_FURTHER_SURFACE_RUNS_UNTIL_DECISION_PACKET_RESOLVED"
                ),
                "surface_evidence_is_nonmoving_under_current_policy": no_tested_surface_movement,
                "decision_matches_declared_default_rule": decision in {
                    "ESCALATE_TO_NEXT_ATTACK_CLASS",
                    "EXECUTE_FILTER_REVISION_PACKET_ONCE",
                    "REPAIR_DECISION_INPUTS_OR_REVIEW_EXHAUSTION_STATE",
                },
            },
            "inputs": {
                "upstream_selected_attack_class": upstream_attack_class,
                "next_cluster_selection_outcome": next_cluster_selection_outcome,
                "next_cluster_next_action": next_cluster_selection.get("summary", {}).get("next_action"),
                "exhausted_cluster_ids": exhausted_cluster_ids,
                "cluster_focus_summaries": cluster_focus_summaries,
                "tested_surface_summaries": tested_surface_summaries,
                "specific_filter_defect_note": specific_filter_defect_note,
                "bounded_filter_revision_packet": bounded_filter_revision_packet,
                "surface_run_hold_policy": surface_run_hold_policy,
                "next_attack_class_if_escalated": next_attack_class_if_escalated,
            },
            "summary": {
                "all_criteria_satisfied": decision in {
                    "ESCALATE_TO_NEXT_ATTACK_CLASS",
                    "EXECUTE_FILTER_REVISION_PACKET_ONCE",
                },
                "phase_status": (
                    "COMPLETE"
                    if decision in {"ESCALATE_TO_NEXT_ATTACK_CLASS", "EXECUTE_FILTER_REVISION_PACKET_ONCE"}
                    else "INCOMPLETE"
                ),
                "next_action": next_action,
            },
        },
        "summary": {
            "program_state": program_state,
            "decision": decision,
            "filter_revision_status": filter_revision_status,
            "no_further_surface_runs_policy": surface_run_hold_policy,
            "tested_surface_count": len(tested_surface_summaries),
            "exhausted_cluster_ids": exhausted_cluster_ids,
            "selected_next_attack_class": selected_next_attack_class,
            "next_attack_class_status": next_attack_class_if_escalated,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "current_attack_class_decision_report": _ptr(current_attack_class_decision_path),
            "next_cluster_selection_report": _ptr(next_cluster_selection_path),
            "cluster_focus_reports": [_ptr(path) for path in cluster_focus_paths],
            "surface_ruling_reports": [_ptr(path) for path in surface_ruling_paths],
        },
        "non_claim_boundary": "Repository-local proof-debt program exhaustion decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt program exhaustion decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "proof_debt_program_exhaustion_decision_20260411_v0.json",
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
        "proof_debt_program_exhaustion_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
