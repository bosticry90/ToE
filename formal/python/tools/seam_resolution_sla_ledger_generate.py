from __future__ import annotations

import argparse
import json
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SEAM_RESOLUTION_SLA_LEDGER_20260416_v0"

COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
DASHBOARD_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
HOLD_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_PACKET41_PACKET42_HOLD_RECONSIDERATION_POLICY_20260408_v0.md"
CLOSURE_OWNER_MAP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"
SEAM_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"

ACTIVE_LANE_REVIEW_HOURS = 24
HELD_LANE_REVIEW_HOURS = 168
ESCALATION_AFTER_WINDOWS = 2
DECISION_OWNER_ROLE = "WS_10_LANE_AUTHORITY_OWNER"


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _resolve_timestamp(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _owner_rows_by_id(owner_map: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = owner_map.get("rows", [])
    if not isinstance(rows, list):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for entry in rows:
        if not isinstance(entry, dict):
            continue
        row_id = str(entry.get("row_id", "")).strip()
        if not row_id:
            continue
        out[row_id] = entry
    return out


def _parse_completion_rows(matrix_path: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for line in _read_text(matrix_path).splitlines():
        if not line.startswith("| ROW-"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 8:
            continue
        rows.append(
            {
                "row_id": cells[0],
                "domain": cells[1],
                "lane": cells[2],
                "current_status": cells[3],
                "blocker_class": cells[4],
                "primary_target": cells[5],
                "primary_artifact": cells[6],
                "primary_gate": cells[7],
                "governance_checkpoint_status": cells[8] if len(cells) > 8 else "UNSPECIFIED",
                "physics_checkpoint_status": cells[9] if len(cells) > 9 else "UNSPECIFIED",
                "gate_runtime_status": cells[10] if len(cells) > 10 else "UNSPECIFIED",
            }
        )
    return [row for row in rows if row["domain"] == "seam"]


def _parse_markdown_tables(text: str) -> list[dict[str, Any]]:
    lines = text.splitlines()
    tables: list[dict[str, Any]] = []
    index = 0
    while index < len(lines):
        if not lines[index].startswith("|"):
            index += 1
            continue
        if index + 1 >= len(lines) or not lines[index + 1].startswith("|"):
            index += 1
            continue
        header = [cell.strip() for cell in lines[index].strip().strip("|").split("|")]
        divider = [cell.strip() for cell in lines[index + 1].strip().strip("|").split("|")]
        if not header or not divider or not all(cell.replace("-", "") == "" for cell in divider):
            index += 1
            continue
        index += 2
        rows: list[dict[str, str]] = []
        while index < len(lines) and lines[index].startswith("|"):
            values = [cell.strip() for cell in lines[index].strip().strip("|").split("|")]
            if len(values) == len(header):
                rows.append(dict(zip(header, values, strict=False)))
            index += 1
        tables.append({"headers": header, "rows": rows})
    return tables


def _clean_md_cell(value: str) -> str:
    return value.strip().strip("`")


def _parse_seam_inventory(path: Path) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    class_rows: dict[str, dict[str, Any]] = {}
    split_rows: dict[str, dict[str, Any]] = {}
    for table in _parse_markdown_tables(_read_text(path)):
        headers = table["headers"]
        rows = table["rows"]
        if headers == ["seam_id", "class", "seam_class_token", "witness_route_status", "source_artifacts", "promotion_candidate"]:
            for row in rows:
                seam_id = _clean_md_cell(str(row.get("seam_id", "")))
                if seam_id:
                    class_rows[seam_id] = {key: _clean_md_cell(str(value)) for key, value in row.items()}
        if headers == ["seam_id", "governance_complete", "physics_complete", "status_read"]:
            for row in rows:
                seam_id = _clean_md_cell(str(row.get("seam_id", "")))
                if seam_id:
                    split_rows[seam_id] = {
                        **{key: _clean_md_cell(str(value)) for key, value in row.items()},
                        "governance_complete": _clean_md_cell(str(row.get("governance_complete", ""))).upper() == "YES",
                        "physics_complete": _clean_md_cell(str(row.get("physics_complete", ""))).upper() == "YES",
                    }
    return class_rows, split_rows


def _seam_id_from_row_id(row_id: str) -> str | None:
    parts = [part for part in row_id.split("-") if part]
    if len(parts) < 5 or parts[0] != "ROW" or parts[1] != "SEAM":
        return None
    return f"SEAM-{'-'.join(parts[2:-1])}"


def _parse_policy_tokens(policy_text: str) -> dict[str, Any]:
    cadence_line = "Review cadence: every 24 hours while lane remains active."
    escalation_line = "Escalation window: if state does not transition after two consecutive review windows, require explicit branch decision artifact in release surfaces."
    owner_line = "Decision owner: WS-10 lane authority owner."
    if cadence_line not in policy_text or escalation_line not in policy_text or owner_line not in policy_text:
        raise ValueError("Hold reconsideration policy missing required cadence, escalation, or owner text.")
    return {
        "decision_owner_role": DECISION_OWNER_ROLE,
        "active_lane_review_hours": ACTIVE_LANE_REVIEW_HOURS,
        "held_lane_review_hours": HELD_LANE_REVIEW_HOURS,
        "escalation_after_windows": ESCALATION_AFTER_WINDOWS,
    }


def _classify_row(*, row: dict[str, str], dashboard: dict[str, Any], seam_class_entry: dict[str, Any], seam_split_entry: dict[str, Any]) -> tuple[str, int, str, str, bool]:
    movement_status = str(dashboard.get("blocker_scoreboard", {}).get("movement_status", "UNKNOWN"))
    exception_required = bool(dashboard.get("blocker_scoreboard", {}).get("exception_required", False))
    stale_inputs = bool(dashboard.get("source_freshness", {}).get("stale_input_warning", False))
    witness_route_status = str(seam_class_entry.get("witness_route_status", "")).strip()
    seam_status_read = str(seam_split_entry.get("status_read", "")).strip()
    governance_complete = bool(seam_split_entry.get("governance_complete"))
    physics_complete = bool(seam_split_entry.get("physics_complete"))

    is_external_hold = witness_route_status == "HOLD_FOR_SCALAR_PUBLICATION_v0" or "HELD_FOR_SCALAR_PUBLICATION" in seam_status_read

    if is_external_hold:
        state = "HOLD_RETAINED_EXTERNAL_HOLD_RELEASE_REQUIRED"
        cadence_hours = HELD_LANE_REVIEW_HOURS
        row_activity_classification = "HELD_EXTERNAL"
    elif row["blocker_class"] == "PARITY_DRIFT":
        state = "HOLD_RETAINED_PARITY_RESTORE_REQUIRED"
        cadence_hours = HELD_LANE_REVIEW_HOURS
        row_activity_classification = "HELD_PARITY_RESTORE"
    elif governance_complete and not physics_complete:
        state = "ACTIVE_TRACK_GOVERNANCE_COMPLETE_PHYSICS_INCOMPLETE"
        cadence_hours = ACTIVE_LANE_REVIEW_HOURS
        row_activity_classification = "ACTIVE_SPLIT_COMPLETE"
    elif movement_status == "DECREASING":
        state = "BOUNDED_CONTINUATION_REVIEW_ELIGIBLE"
        cadence_hours = ACTIVE_LANE_REVIEW_HOURS
        row_activity_classification = "ACTIVE_ELIGIBLE"
    elif movement_status == "INCREASING":
        state = "SCOPE_REDUCTION_REMEDIATION_REVIEW_REQUIRED"
        cadence_hours = ACTIVE_LANE_REVIEW_HOURS
        row_activity_classification = "ACTIVE_REMEDIATION"
    elif exception_required:
        state = "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION"
        cadence_hours = ACTIVE_LANE_REVIEW_HOURS
        row_activity_classification = "ACTIVE_TRACKED"
    else:
        state = "ACTIVE_TRACK_AWAITING_EVIDENCE_REVIEW"
        cadence_hours = HELD_LANE_REVIEW_HOURS
        row_activity_classification = "ACTIVE_TRACKED"

    freshness_status = "STALE_INPUTS_PRESENT" if stale_inputs else "INPUTS_CURRENT_ENOUGH_FOR_REVIEW"
    return state, cadence_hours, freshness_status, row_activity_classification, is_external_hold


def build_seam_sla_ledger(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    dashboard = _read_json(DASHBOARD_REPORT_PATH)
    policy = _parse_policy_tokens(_read_text(HOLD_POLICY_PATH))
    owner_map = _read_json(CLOSURE_OWNER_MAP_PATH)
    owner_rows = _owner_rows_by_id(owner_map)
    seam_class_rows, seam_split_rows = _parse_seam_inventory(SEAM_INVENTORY_PATH)
    seam_rows = _parse_completion_rows(COMPLETION_MATRIX_PATH)
    if not seam_rows:
        raise ValueError("Completion matrix produced zero seam rows.")

    review_timestamp = datetime.strptime(_resolve_timestamp(captured_at_utc), "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    entries: list[dict[str, Any]] = []
    active_rows = 0
    held_rows = 0
    missing_owner_rows: list[str] = []
    missing_seam_status_rows: list[str] = []
    for row in seam_rows:
        owner_entry = owner_rows.get(row["row_id"])
        if owner_entry is None:
            missing_owner_rows.append(row["row_id"])
            owner_entry = {}
        seam_id = _seam_id_from_row_id(row["row_id"])
        seam_class_entry = seam_class_rows.get(seam_id or "", {})
        seam_split_entry = seam_split_rows.get(seam_id or "", {})
        seam_status_resolution = "CANONICAL_SEAM_STATUS_PINNED"
        if not seam_class_entry or not seam_split_entry:
            seam_status_resolution = "MISSING_CANONICAL_SEAM_STATUS"
            missing_seam_status_rows.append(row["row_id"])
        decision_state, cadence_hours, freshness_status, row_activity_classification, is_external_hold = _classify_row(
            row=row,
            dashboard=dashboard,
            seam_class_entry=seam_class_entry,
            seam_split_entry=seam_split_entry,
        )
        next_review = review_timestamp + timedelta(hours=cadence_hours)
        escalation_due = review_timestamp + timedelta(hours=cadence_hours * policy["escalation_after_windows"])
        if cadence_hours == ACTIVE_LANE_REVIEW_HOURS:
            active_rows += 1
        else:
            held_rows += 1
        entries.append(
            {
                "row_id": row["row_id"],
                "seam_id": seam_id,
                "seam_class": str(seam_class_entry.get("class", "")).strip() or "UNSPECIFIED",
                "witness_route_status": str(seam_class_entry.get("witness_route_status", "")).strip() or None,
                "promotion_candidate": str(seam_class_entry.get("promotion_candidate", "")).strip() or None,
                "governance_complete": seam_split_entry.get("governance_complete"),
                "physics_complete": seam_split_entry.get("physics_complete"),
                "seam_status_read": str(seam_split_entry.get("status_read", "")).strip() or None,
                "seam_status_resolution": seam_status_resolution,
                "lane": row["lane"],
                "blocker_class": row["blocker_class"],
                "current_status": row["current_status"],
                "governance_checkpoint_status": row.get("governance_checkpoint_status"),
                "physics_checkpoint_status": row.get("physics_checkpoint_status"),
                "gate_runtime_status": row.get("gate_runtime_status"),
                "row_activity_classification": row_activity_classification,
                "is_external_hold": is_external_hold,
                "decision_owner_role": policy["decision_owner_role"],
                "primary_owner": str(owner_entry.get("primary_owner", "")).strip() or None,
                "secondary_owner": str(owner_entry.get("secondary_owner", "")).strip() or None,
                "decision_state": decision_state,
                "review_cadence_hours": cadence_hours,
                "review_timestamp_utc": review_timestamp.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "next_review_due_utc": next_review.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "escalation_due_utc": escalation_due.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "freshness_status": freshness_status,
                "dashboard_movement_status": str(dashboard.get("blocker_scoreboard", {}).get("movement_status", "")),
                "dashboard_exception_required": bool(dashboard.get("blocker_scoreboard", {}).get("exception_required", False)),
                "required_evidence_surface": str(owner_entry.get("required_evidence_surface", row["primary_target"])),
                "exit_criterion": str(owner_entry.get("exit_criterion", "")).strip() or None,
                "target_surface": row["primary_target"],
                "artifact_surface": row["primary_artifact"],
                "gate_surface": row["primary_gate"],
            }
        )

    owner_completion_rate = round((len(seam_rows) - len(missing_owner_rows)) / len(seam_rows), 2)
    seam_status_coverage_rate = round((len(seam_rows) - len(missing_seam_status_rows)) / len(seam_rows), 2)

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": review_timestamp.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "policy": {
            **policy,
            "decision_owner_assignment_status": (
                "NAMED_OWNERS_ASSIGNED" if not missing_owner_rows else "ROLE_ONLY_PENDING_NAMED_ASSIGNMENT"
            ),
        },
        "dashboard_coupling": {
            "dashboard_pointer": _ptr(DASHBOARD_REPORT_PATH),
            "movement_status": str(dashboard.get("blocker_scoreboard", {}).get("movement_status", "")),
            "net_delta": int(dashboard.get("blocker_scoreboard", {}).get("net_delta", 0) or 0),
            "exception_required": bool(dashboard.get("blocker_scoreboard", {}).get("exception_required", False)),
            "stale_input_warning": bool(dashboard.get("source_freshness", {}).get("stale_input_warning", False)),
        },
        "summary": {
            "seam_rows_total": len(entries),
            "active_review_rows": active_rows,
            "held_review_rows": held_rows,
            "external_hold_rows": sum(1 for entry in entries if entry["is_external_hold"]),
            "split_completion_rows": sum(
                1 for entry in entries if entry["governance_complete"] is True and entry["physics_complete"] is False
            ),
            "decision_states_present": sorted({entry["decision_state"] for entry in entries}),
            "missing_owner_rows": sorted(missing_owner_rows),
            "owner_completion_rate": owner_completion_rate,
            "missing_seam_status_rows": sorted(missing_seam_status_rows),
            "seam_status_coverage_rate": seam_status_coverage_rate,
        },
        "entries": entries,
        "source_bundle": {
            "completion_matrix": _ptr(COMPLETION_MATRIX_PATH),
            "blocker_burn_dashboard": _ptr(DASHBOARD_REPORT_PATH),
            "hold_reconsideration_policy": _ptr(HOLD_POLICY_PATH),
            "closure_owner_map": _ptr(CLOSURE_OWNER_MAP_PATH),
            "seam_inventory": _ptr(SEAM_INVENTORY_PATH),
        },
        "non_claim_boundary": "This seam SLA ledger is a repository-local cadence and review artifact and does not authorize seam continuation by itself.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate seam-resolution SLA ledger report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_seam_sla_ledger(output_path=out, captured_at_utc=ns.captured_at_utc)
    print(
        "seam_resolution_sla_ledger_generate: "
        f"rows={payload['summary']['seam_rows_total']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())