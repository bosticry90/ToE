from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_SCHEMA = REPO_ROOT / "formal" / "docs" / "release" / "STATE_CORE_SCHEMA_v0.json"
DEFAULT_STATE_CORE = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _ensure(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _validate_state_core(schema: dict[str, Any], state_core: dict[str, Any]) -> None:
    for key in schema["required_top_level"]:
        _ensure(key in state_core, f"Missing top-level key: {key}")

    _ensure(
        state_core["schema_id"] == schema["schema_id"],
        "state_core schema_id mismatch",
    )

    _ensure(
        len([state_core["active_lane"]]) <= int(schema["max_active_lanes"]),
        "max_active_lanes violated",
    )

    _ensure(
        len(state_core["queued_lanes"]) <= int(schema["max_queued_lanes"]),
        "max_queued_lanes violated",
    )

    _ensure(
        state_core["active_tranche_id"],
        "active_tranche_id must be set",
    )

    family = state_core["ws10_branch_boundary_status_family"]
    _ensure("family_id" in family, "ws10_branch_boundary_status_family missing family_id")
    _ensure("active_decision_id" in family, "ws10_branch_boundary_status_family missing active_decision_id")
    _ensure("decision_chain" in family, "ws10_branch_boundary_status_family missing decision_chain")
    _ensure(len(family["decision_chain"]) >= 1, "ws10_branch_boundary_status_family decision_chain cannot be empty")
    decision_ids = [entry["id"] for entry in family["decision_chain"]]
    _ensure(
        family["active_decision_id"] in decision_ids,
        "ws10_branch_boundary_status_family active_decision_id must appear in decision_chain",
    )

    task_family = state_core["ws10_task_status_table_family"]
    _ensure("family_id" in task_family, "ws10_task_status_table_family missing family_id")
    _ensure("active_task_ids" in task_family, "ws10_task_status_table_family missing active_task_ids")
    _ensure("rows" in task_family, "ws10_task_status_table_family missing rows")
    _ensure(len(task_family["rows"]) >= 1, "ws10_task_status_table_family rows cannot be empty")
    task_ids = [entry["id"] for entry in task_family["rows"]]
    for active_task_id in task_family["active_task_ids"]:
        _ensure(
            active_task_id in task_ids,
            "ws10_task_status_table_family active_task_ids must appear in rows",
        )

    evidence_family = state_core["ws10_evidence_log_family"]
    _ensure("family_id" in evidence_family, "ws10_evidence_log_family missing family_id")
    _ensure("active_entry_id" in evidence_family, "ws10_evidence_log_family missing active_entry_id")
    _ensure("entries" in evidence_family, "ws10_evidence_log_family missing entries")
    _ensure(len(evidence_family["entries"]) >= 1, "ws10_evidence_log_family entries cannot be empty")
    evidence_ids = [entry["id"] for entry in evidence_family["entries"]]
    _ensure(
        evidence_family["active_entry_id"] in evidence_ids,
        "ws10_evidence_log_family active_entry_id must appear in entries",
    )

    lineage_family = state_core["ws10_scientific_artifact_lineage_family"]
    _ensure("family_id" in lineage_family, "ws10_scientific_artifact_lineage_family missing family_id")
    _ensure("active_lineage_id" in lineage_family, "ws10_scientific_artifact_lineage_family missing active_lineage_id")
    _ensure("lineages" in lineage_family, "ws10_scientific_artifact_lineage_family missing lineages")
    _ensure(
        len(lineage_family["lineages"]) >= 1,
        "ws10_scientific_artifact_lineage_family lineages cannot be empty",
    )
    lineage_ids = [entry["id"] for entry in lineage_family["lineages"]]
    _ensure(
        lineage_family["active_lineage_id"] in lineage_ids,
        "ws10_scientific_artifact_lineage_family active_lineage_id must appear in lineages",
    )
    for lineage_entry in lineage_family["lineages"]:
        for field in ["id", "tranche_id", "lane", "cycle", "artifact", "lineage_role"]:
            _ensure(
                field in lineage_entry,
                f"ws10_scientific_artifact_lineage_family entry missing field: {field}",
            )

    recent_chain = state_core["recent_tranche_chain_by_lane"][state_core["active_lane"]]
    _ensure(
        state_core["active_tranche_id"] in recent_chain,
        "active_tranche_id must appear in recent_tranche_chain_by_lane for active lane",
    )

    for tranche in state_core["tranches"]:
        for field in schema["required_tranche_fields"]:
            _ensure(field in tranche, f"tranche missing required field: {field}")

        _ensure(
            tranche["mode"] in schema["allowed_modes"],
            f"invalid tranche mode: {tranche['mode']}",
        )

        _ensure(
            tranche["scientific_delta_class"] in schema["allowed_scientific_delta_classes"],
            f"invalid scientific_delta_class: {tranche['scientific_delta_class']}",
        )

        transition = tranche["status_transition"]
        for transition_field in ["from", "to", "decision_basis"]:
            _ensure(
                transition_field in transition,
                f"status_transition missing field: {transition_field}",
            )

        _ensure(
            transition["from"] in schema["allowed_status_postures"],
            f"invalid transition from posture: {transition['from']}",
        )
        _ensure(
            transition["to"] in schema["allowed_status_postures"],
            f"invalid transition to posture: {transition['to']}",
        )


def _status_family_summary(state_core: dict[str, Any]) -> tuple[str, str, str]:
    family = state_core["ws10_branch_boundary_status_family"]
    active = family["active_decision_id"]
    chain = family["decision_chain"]
    chain_compact = " -> ".join(f"{entry['id']}:{entry['kind']}" for entry in chain)
    active_entry = next(entry for entry in chain if entry["id"] == active)
    active_status = active_entry["status"]
    return active, active_status, chain_compact


def _task_status_family_summary(state_core: dict[str, Any]) -> tuple[str, int, int, str]:
    family = state_core["ws10_task_status_table_family"]
    rows = family["rows"]
    active_task_ids = family["active_task_ids"]
    row_count = len(rows)
    done_count = sum(1 for row in rows if row["status"] == "DONE")
    active_tasks_text = ", ".join(active_task_ids) if active_task_ids else "NONE"
    task_chain = " -> ".join(f"{row['id']}:{row['status']}" for row in rows)
    return active_tasks_text, row_count, done_count, task_chain


def _evidence_log_family_summary(state_core: dict[str, Any]) -> tuple[str, str, int, str]:
    family = state_core["ws10_evidence_log_family"]
    entries = family["entries"]
    active_entry_id = family["active_entry_id"]
    active_entry = next(entry for entry in entries if entry["id"] == active_entry_id)
    entry_count = len(entries)
    evidence_chain = " -> ".join(f"{entry['id']}:{entry['task_id']}" for entry in entries)
    return active_entry_id, active_entry["task_id"], entry_count, evidence_chain


def _scientific_artifact_lineage_family_summary(state_core: dict[str, Any]) -> tuple[str, str, str, int, str]:
    family = state_core["ws10_scientific_artifact_lineage_family"]
    lineages = family["lineages"]
    active_lineage_id = family["active_lineage_id"]
    active_lineage = next(entry for entry in lineages if entry["id"] == active_lineage_id)
    lineage_count = len(lineages)
    lineage_chain = " -> ".join(f"{entry['id']}:{entry['tranche_id']}" for entry in lineages)
    return active_lineage_id, active_lineage["tranche_id"], active_lineage["artifact"], lineage_count, lineage_chain


def _find_active_tranche(state_core: dict[str, Any]) -> dict[str, Any]:
    active_tranche_id = state_core["active_tranche_id"]
    active_lane = state_core["active_lane"]
    for tranche in state_core["tranches"]:
        if tranche["id"] == active_tranche_id:
            _ensure(
                tranche["lane"] == active_lane,
                "active_tranche_id does not belong to active_lane",
            )
            return tranche
    raise ValueError(f"active_tranche_id not found in tranches: {active_tranche_id}")


def _render_state_snippet(state_core: dict[str, Any]) -> str:
    active = state_core["active_lane"]
    queued = ", ".join(state_core["queued_lanes"]) if state_core["queued_lanes"] else "NONE"
    active_lane_data = state_core["lanes"][active]
    queued_lane_details: list[str] = []
    for lane in state_core["queued_lanes"]:
        lane_data = state_core["lanes"][lane]
        queued_lane_details.append(
            f"{lane}:{lane_data['status']}@{lane_data['active_cycle']}[{lane_data['boundary']}]"
        )
    queued_details = "; ".join(queued_lane_details) if queued_lane_details else "NONE"
    queued_chain_summary: list[str] = []
    for lane in state_core["queued_lanes"]:
        chain = ",".join(state_core["recent_tranche_chain_by_lane"][lane])
        queued_chain_summary.append(f"{lane}={chain}")
    queued_chain_text = " | ".join(queued_chain_summary) if queued_chain_summary else "NONE"
    active_decision, active_decision_status, _ = _status_family_summary(state_core)

    return "\n".join(
        [
            "<!-- GENERATED: STATE_CORE_ACTIVE_LANE_v0 -->",
            f"- `STATE_CORE_ACTIVE_LANE_v0: {active}`",
            f"- `STATE_CORE_ACTIVE_STATUS_v0: {active_lane_data['status']}`",
            f"- `STATE_CORE_ACTIVE_CYCLE_v0: {active_lane_data['active_cycle']}`",
            f"- `STATE_CORE_BOUNDARY_v0: {active_lane_data['boundary']}`",
            f"- `STATE_CORE_NEXT_DECISION_v0: {active_lane_data['next_decision']}`",
            f"- `STATE_CORE_QUEUED_LANES_v0: {queued}`",
            f"- `STATE_CORE_QUEUED_LANE_DETAILS_v0: {queued_details}`",
            f"- `STATE_CORE_QUEUED_CHAIN_v0: {queued_chain_text}`",
            f"- `STATE_CORE_BRANCH_BOUNDARY_ACTIVE_DECISION_v0: {active_decision}`",
            f"- `STATE_CORE_BRANCH_BOUNDARY_ACTIVE_STATUS_v0: {active_decision_status}`",
            "<!-- /GENERATED: STATE_CORE_ACTIVE_LANE_v0 -->",
        ]
    )


def _render_roadmap_snippet(state_core: dict[str, Any]) -> str:
    active = state_core["active_lane"]
    tranche = _find_active_tranche(state_core)
    _, _, chain_compact = _status_family_summary(state_core)
    return "\n".join(
        [
            "<!-- GENERATED: STATE_CORE_ROADMAP_STATUS_v0 -->",
            f"- `STATE_CORE_ROADMAP_ACTIVE_LANE_v0: {active}`",
            f"- `STATE_CORE_ROADMAP_ACTIVE_TRANCHE_v0: {tranche['id']}`",
            f"- `STATE_CORE_ROADMAP_MODE_v0: {tranche['mode']}`",
            f"- `STATE_CORE_ROADMAP_DELTA_CLASS_v0: {tranche['scientific_delta_class']}`",
            f"- `STATE_CORE_ROADMAP_BRANCH_CHAIN_v0: {chain_compact}`",
            "<!-- /GENERATED: STATE_CORE_ROADMAP_STATUS_v0 -->",
        ]
    )


def _render_tracker_snippet(state_core: dict[str, Any]) -> str:
    tranche = _find_active_tranche(state_core)
    active_decision, active_decision_status, _ = _status_family_summary(state_core)
    active_tasks_text, row_count, done_count, _ = _task_status_family_summary(state_core)
    active_evidence_id, active_evidence_task_id, evidence_count, _ = _evidence_log_family_summary(state_core)
    active_lineage_id, active_lineage_tranche_id, active_lineage_artifact, lineage_count, _ = _scientific_artifact_lineage_family_summary(state_core)
    return "\n".join(
        [
            "<!-- GENERATED: STATE_CORE_TRACKER_STATUS_v0 -->",
            f"- `STATE_CORE_TRACKER_ACTIVE_TRANCHE_v0: {tranche['id']}`",
            f"- `STATE_CORE_TRACKER_GATE_v0: {tranche['gate_test']}`",
            f"- `STATE_CORE_TRACKER_ARTIFACT_v0: {tranche['evidence_artifact']}`",
            f"- `STATE_CORE_TRACKER_TRANSITION_v0: {tranche['status_transition']['from']}_TO_{tranche['status_transition']['to']}`",
            f"- `STATE_CORE_TRACKER_BRANCH_DECISION_v0: {active_decision}`",
            f"- `STATE_CORE_TRACKER_BRANCH_STATUS_v0: {active_decision_status}`",
            f"- `STATE_CORE_TRACKER_WS10_ACTIVE_TASKS_v0: {active_tasks_text}`",
            f"- `STATE_CORE_TRACKER_WS10_TASK_ROWS_v0: {row_count}`",
            f"- `STATE_CORE_TRACKER_WS10_DONE_TASKS_v0: {done_count}`",
            f"- `STATE_CORE_TRACKER_WS10_EVIDENCE_ACTIVE_ENTRY_v0: {active_evidence_id}`",
            f"- `STATE_CORE_TRACKER_WS10_EVIDENCE_ACTIVE_TASK_v0: {active_evidence_task_id}`",
            f"- `STATE_CORE_TRACKER_WS10_EVIDENCE_ENTRY_COUNT_v0: {evidence_count}`",
            f"- `STATE_CORE_TRACKER_WS10_LINEAGE_ACTIVE_ID_v0: {active_lineage_id}`",
            f"- `STATE_CORE_TRACKER_WS10_LINEAGE_ACTIVE_TRANCHE_v0: {active_lineage_tranche_id}`",
            f"- `STATE_CORE_TRACKER_WS10_LINEAGE_ACTIVE_ARTIFACT_v0: {active_lineage_artifact}`",
            f"- `STATE_CORE_TRACKER_WS10_LINEAGE_ENTRY_COUNT_v0: {lineage_count}`",
            "<!-- /GENERATED: STATE_CORE_TRACKER_STATUS_v0 -->",
        ]
    )


def _render_ws10_snippet(state_core: dict[str, Any]) -> str:
    tranche = _find_active_tranche(state_core)
    active_decision, _, chain_compact = _status_family_summary(state_core)
    active_tasks_text, row_count, done_count, task_chain = _task_status_family_summary(state_core)
    active_evidence_id, active_evidence_task_id, evidence_count, evidence_chain = _evidence_log_family_summary(state_core)
    active_lineage_id, active_lineage_tranche_id, active_lineage_artifact, lineage_count, lineage_chain = _scientific_artifact_lineage_family_summary(state_core)
    return "\n".join(
        [
            "<!-- GENERATED: STATE_CORE_WS10_STATUS_v0 -->",
            f"- `STATE_CORE_WS10_ACTIVE_TRANCHE_v0: {tranche['id']}`",
            f"- `STATE_CORE_WS10_PREDECESSOR_v0: {tranche['predecessor']}`",
            f"- `STATE_CORE_WS10_STOP_CONDITION_v0: {tranche['stop_condition']}`",
            f"- `STATE_CORE_WS10_ACTIVE_DECISION_v0: {active_decision}`",
            f"- `STATE_CORE_WS10_BRANCH_CHAIN_v0: {chain_compact}`",
            f"- `STATE_CORE_WS10_ACTIVE_TASKS_v0: {active_tasks_text}`",
            f"- `STATE_CORE_WS10_TASK_ROW_COUNT_v0: {row_count}`",
            f"- `STATE_CORE_WS10_DONE_TASK_COUNT_v0: {done_count}`",
            f"- `STATE_CORE_WS10_TASK_STATUS_CHAIN_v0: {task_chain}`",
            f"- `STATE_CORE_WS10_EVIDENCE_ACTIVE_ENTRY_v0: {active_evidence_id}`",
            f"- `STATE_CORE_WS10_EVIDENCE_ACTIVE_TASK_v0: {active_evidence_task_id}`",
            f"- `STATE_CORE_WS10_EVIDENCE_ENTRY_COUNT_v0: {evidence_count}`",
            f"- `STATE_CORE_WS10_EVIDENCE_CHAIN_v0: {evidence_chain}`",
            f"- `STATE_CORE_WS10_LINEAGE_ACTIVE_ID_v0: {active_lineage_id}`",
            f"- `STATE_CORE_WS10_LINEAGE_ACTIVE_TRANCHE_v0: {active_lineage_tranche_id}`",
            f"- `STATE_CORE_WS10_LINEAGE_ACTIVE_ARTIFACT_v0: {active_lineage_artifact}`",
            f"- `STATE_CORE_WS10_LINEAGE_ENTRY_COUNT_v0: {lineage_count}`",
            f"- `STATE_CORE_WS10_LINEAGE_CHAIN_v0: {lineage_chain}`",
            "<!-- /GENERATED: STATE_CORE_WS10_STATUS_v0 -->",
        ]
    )


def _write_output(output_dir: Path, filename: str, content: str) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / filename).write_text(content + "\n", encoding="utf-8")


def _replace_generated_block(text: str, marker_id: str, replacement: str) -> str:
    begin = f"<!-- GENERATED: {marker_id} -->"
    end = f"<!-- /GENERATED: {marker_id} -->"
    pattern = re.compile(rf"{re.escape(begin)}.*?{re.escape(end)}", re.DOTALL)
    _ensure(
        pattern.search(text) is not None,
        f"Could not locate generated block markers for {marker_id}",
    )
    return pattern.sub(replacement, text, count=1)


def _apply_mirror_targets(state_core: dict[str, Any], snippets_by_marker: dict[str, str]) -> None:
    for target in state_core["mirror_targets"]:
        marker_id = target["marker_id"]
        path = REPO_ROOT / target["path"]
        text = path.read_text(encoding="utf-8")
        updated = _replace_generated_block(text, marker_id, snippets_by_marker[marker_id])
        path.write_text(updated, encoding="utf-8")


def _verify_mirror_targets(state_core: dict[str, Any], snippets_by_marker: dict[str, str]) -> None:
    for target in state_core["mirror_targets"]:
        marker_id = target["marker_id"]
        path = REPO_ROOT / target["path"]
        text = path.read_text(encoding="utf-8")
        expected = _replace_generated_block(text, marker_id, snippets_by_marker[marker_id])
        _ensure(
            expected == text,
            f"Mirror block mismatch for {path} marker {marker_id}; run renderer with --apply-mirrors",
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Render state_core mirror snippets.")
    parser.add_argument("--schema", type=Path, default=DEFAULT_SCHEMA)
    parser.add_argument("--state-core", type=Path, default=DEFAULT_STATE_CORE)
    parser.add_argument("--output-dir", type=Path, default=None)
    parser.add_argument("--print", dest="print_mode", action="store_true")
    parser.add_argument("--apply-mirrors", action="store_true")
    parser.add_argument("--verify-mirrors", action="store_true")
    args = parser.parse_args()

    schema = _load_json(args.schema)
    state_core = _load_json(args.state_core)
    _validate_state_core(schema, state_core)

    snippets = {
        "state_core_state_snippet_v0.md": _render_state_snippet(state_core),
        "state_core_roadmap_snippet_v0.md": _render_roadmap_snippet(state_core),
        "state_core_tracker_snippet_v0.md": _render_tracker_snippet(state_core),
        "state_core_ws10_snippet_v0.md": _render_ws10_snippet(state_core),
    }
    snippets_by_marker = {
        "STATE_CORE_ACTIVE_LANE_v0": snippets["state_core_state_snippet_v0.md"],
        "STATE_CORE_ROADMAP_STATUS_v0": snippets["state_core_roadmap_snippet_v0.md"],
        "STATE_CORE_TRACKER_STATUS_v0": snippets["state_core_tracker_snippet_v0.md"],
        "STATE_CORE_WS10_STATUS_v0": snippets["state_core_ws10_snippet_v0.md"],
    }

    if args.output_dir is None:
        args.output_dir = REPO_ROOT / "formal" / "output" / "state_core_generated"

    for filename, content in snippets.items():
        _write_output(args.output_dir, filename, content)

    if args.apply_mirrors:
        _apply_mirror_targets(state_core, snippets_by_marker)

    if args.verify_mirrors:
        _verify_mirror_targets(state_core, snippets_by_marker)

    if args.print_mode:
        for filename, content in snippets.items():
            print(f"## {filename}")
            print(content)


if __name__ == "__main__":
    main()
