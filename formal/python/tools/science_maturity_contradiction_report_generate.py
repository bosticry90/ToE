from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_MATURITY_CONTRADICTION_REPORT_20260416_v0"

COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
MATURITY_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
SEAM_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json"
DASHBOARD_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
PHYSICS_PROGRESS_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"


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
    return rows


def _pillar_id_from_row_id(row_id: str) -> str | None:
    parts = [part for part in row_id.split("-") if part]
    if len(parts) < 4 or parts[0] != "ROW" or parts[1] != "PILLAR":
        return None
    return f"PILLAR-{parts[2]}"


def _maturity_rows_by_pillar(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = payload.get("pillars", [])
    if not isinstance(rows, list):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        pillar_id = str(row.get("pillar_id", "")).strip()
        if pillar_id:
            out[pillar_id] = row
    return out


def _severity_rank(value: str) -> int:
    return {"LOW": 1, "MEDIUM": 2, "HIGH": 3}.get(value, 0)


def _is_active_row_for_stale_readiness(row: dict[str, Any]) -> bool:
    if not isinstance(row, dict):
        return False
    if str(row.get("promotion_readiness_status", "")).startswith("PATHS_PINNED") is False:
        return False
    if bool(row.get("is_external_hold", False)):
        return False
    runtime_state = str(row.get("gate_runtime_status", "")).strip()
    if runtime_state == "GATE_RUNTIME_RECOMPUTE_MONITORING_REQUIRED":
        return False
    return True


def build_science_maturity_contradiction_report(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    matrix_rows = _parse_completion_rows(COMPLETION_MATRIX_PATH)
    maturity_registry = _read_json(MATURITY_REGISTRY_PATH)
    seam_ledger = _read_json(SEAM_LEDGER_PATH)
    dashboard = _read_json(DASHBOARD_REPORT_PATH)
    physics_progress = _read_json(PHYSICS_PROGRESS_LEDGER_PATH)

    maturity_rows = _maturity_rows_by_pillar(maturity_registry)
    contradictions: list[dict[str, Any]] = []

    for row in matrix_rows:
        if row["domain"] != "pillar" or row["blocker_class"] != "THEOREM_GAP":
            continue
        pillar_id = _pillar_id_from_row_id(row["row_id"])
        pillar = maturity_rows.get(pillar_id or "")
        if not pillar:
            continue
        if str(pillar.get("m4_status", "")).strip() == "COMPLETE_BOUNDED_v0":
            contradictions.append(
                {
                    "contradiction_id": f"CONTRA-PILLAR-{pillar_id}-M4-THEOREM-GAP",
                    "contradiction_type": "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP",
                    "severity": "HIGH",
                    "row_id": row["row_id"],
                    "pillar_id": pillar_id,
                    "live_blocker_class": row["blocker_class"],
                    "live_current_status": row["current_status"],
                    "m4_status": pillar.get("m4_status"),
                    "maturity_program_status": maturity_registry.get("program_status", {}).get("PILLAR_DEEP_MATURITY_PROGRAM_STATUS_v0"),
                }
            )

    seam_entries = seam_ledger.get("entries", [])
    for entry in seam_entries:
        if not isinstance(entry, dict):
            continue
        if entry.get("governance_complete") is True and entry.get("physics_complete") is False:
            contradictions.append(
                {
                    "contradiction_id": f"CONTRA-SEAM-{entry['row_id']}-GOVERNANCE-COMPLETE-PHYSICS-INCOMPLETE",
                    "contradiction_type": "SEAM_GOVERNANCE_COMPLETE_VS_PHYSICS_INCOMPLETE",
                    "severity": "MEDIUM",
                    "row_id": entry["row_id"],
                    "seam_id": entry.get("seam_id"),
                    "decision_state": entry.get("decision_state"),
                    "governance_complete": entry.get("governance_complete"),
                    "physics_complete": entry.get("physics_complete"),
                }
            )
        if entry.get("physics_complete") is True and (
            str(entry.get("decision_state", "")).startswith("HOLD_RETAINED")
            or str(entry.get("blocker_class", "")) in {"PARITY_DRIFT", "SEAM_INTEGRATION_GAP"}
        ):
            contradictions.append(
                {
                    "contradiction_id": f"CONTRA-SEAM-{entry['row_id']}-PHYSICS-COMPLETE-HOLD",
                    "contradiction_type": "SEAM_PHYSICS_COMPLETE_VS_LIVE_HOLD_OR_PARITY",
                    "severity": "HIGH",
                    "row_id": entry["row_id"],
                    "seam_id": entry.get("seam_id"),
                    "decision_state": entry.get("decision_state"),
                    "blocker_class": entry.get("blocker_class"),
                    "physics_complete": entry.get("physics_complete"),
                    "governance_complete": entry.get("governance_complete"),
                }
            )
        if str(entry.get("seam_status_resolution", "")) == "MISSING_CANONICAL_SEAM_STATUS":
            contradictions.append(
                {
                    "contradiction_id": f"CONTRA-SEAM-{entry['row_id']}-MISSING-CANONICAL-STATUS",
                    "contradiction_type": "LIVE_SEAM_ROW_MISSING_CANONICAL_STATUS",
                    "severity": "HIGH",
                    "row_id": entry["row_id"],
                    "seam_id": entry.get("seam_id"),
                    "lane": entry.get("lane"),
                    "seam_status_resolution": entry.get("seam_status_resolution"),
                }
            )

    readiness_rows = dashboard.get("row_promotion_readiness", {}).get("rows", [])
    seam_entries_by_row = {
        str(entry.get("row_id", "")): entry for entry in seam_entries if isinstance(entry, dict) and entry.get("row_id")
    }
    stale_ready_rows = []
    for row in readiness_rows:
        if not _is_active_row_for_stale_readiness(row):
            continue
        row_id = str(row.get("row_id", ""))
        seam_entry = seam_entries_by_row.get(row_id)
        if seam_entry is not None and str(seam_entry.get("row_activity_classification", "")).startswith("HELD_"):
            continue
        stale_ready_rows.append(row_id)
    if bool(dashboard.get("blocker_scoreboard", {}).get("exception_required", False)) and bool(
        dashboard.get("source_freshness", {}).get("stale_input_warning", False)
    ) and stale_ready_rows:
        contradictions.append(
            {
                "contradiction_id": "CONTRA-GLOBAL-STALE-READINESS-SIGNAL",
                "contradiction_type": "STALE_READINESS_SIGNAL_WITH_PATHS_PINNED",
                "severity": "MEDIUM",
                "row_ids": sorted(stale_ready_rows),
                "movement_status": dashboard.get("blocker_scoreboard", {}).get("movement_status"),
                "exception_required": dashboard.get("blocker_scoreboard", {}).get("exception_required"),
                "stale_input_warning": dashboard.get("source_freshness", {}).get("stale_input_warning"),
            }
        )

    severities = sorted({entry["severity"] for entry in contradictions}, key=_severity_rank)
    contradiction_types = sorted({entry["contradiction_type"] for entry in contradictions})
    highest_severity = severities[-1] if severities else "NONE"
    captured = _resolve_timestamp(captured_at_utc)

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured,
        "contradiction_status": "FAIL_CLOSED_CONTRADICTIONS_PRESENT" if contradictions else "NO_CONTRADICTIONS_DETECTED",
        "fail_conditions": [
            "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP",
            "SEAM_PHYSICS_COMPLETE_VS_LIVE_HOLD_OR_PARITY",
            "LIVE_SEAM_ROW_MISSING_CANONICAL_STATUS",
            "STALE_READINESS_SIGNAL_WITH_PATHS_PINNED",
        ],
        "summary": {
            "contradictions_total": len(contradictions),
            "contradiction_types_present": contradiction_types,
            "highest_severity": highest_severity,
            "matrix_rows_evaluated": len(matrix_rows),
            "pillar_rows_evaluated": len([row for row in matrix_rows if row["domain"] == "pillar"]),
            "seam_rows_evaluated": len(seam_entries),
            "active_stale_ready_rows": len(stale_ready_rows),
            "live_blocker_state_change": physics_progress.get("actual_blocker_state_change"),
            "live_progress_classification": physics_progress.get("progress_classification"),
        },
        "contradictions": contradictions,
        "source_bundle": {
            "completion_matrix": _ptr(COMPLETION_MATRIX_PATH),
            "maturity_registry": _ptr(MATURITY_REGISTRY_PATH),
            "seam_resolution_sla_ledger": _ptr(SEAM_LEDGER_PATH),
            "blocker_burn_dashboard": _ptr(DASHBOARD_REPORT_PATH),
            "physics_progress_ledger": _ptr(PHYSICS_PROGRESS_LEDGER_PATH),
        },
        "non_claim_boundary": "This contradiction report is a repository-local consistency surface and does not alter scientific authority or release-gate truth by itself.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate science maturity contradiction report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_maturity_contradiction_report_20260416_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_science_maturity_contradiction_report(output_path=out, captured_at_utc=ns.captured_at_utc)
    print(
        "science_maturity_contradiction_report_generate: "
        f"contradictions={payload['summary']['contradictions_total']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())