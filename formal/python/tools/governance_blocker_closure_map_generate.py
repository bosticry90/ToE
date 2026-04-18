from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_BLOCKER_CLOSURE_MAP_20260410_v0"

COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
CLOSURE_OWNER_MAP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _parse_completion_rows(matrix_path: Path) -> list[dict[str, str]]:
    if not matrix_path.exists():
        raise FileNotFoundError(f"Missing required file: {matrix_path}")

    rows: list[dict[str, str]] = []
    for line in matrix_path.read_text(encoding="utf-8").splitlines():
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


def _is_closed_monitoring_row(row: dict[str, str]) -> bool:
    return (
        row.get("governance_checkpoint_status") == "GOVERNANCE_COMPLETE"
        and row.get("physics_checkpoint_status") == "PHYSICS_COMPLETE"
        and row.get("gate_runtime_status") == "GATE_RUNTIME_RECOMPUTE_MONITORING_REQUIRED"
    )


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


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_blocker_closure_map(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    completion_rows = _parse_completion_rows(COMPLETION_MATRIX_PATH)
    owner_map = _read_json(CLOSURE_OWNER_MAP_PATH)
    owner_rows = _owner_rows_by_id(owner_map)

    mappings: list[dict[str, Any]] = []
    missing_owner_rows: list[str] = []
    for row in completion_rows:
        owner_row = owner_rows.get(row["row_id"])
        if owner_row is None:
            missing_owner_rows.append(row["row_id"])
            owner_row = {}

        counts_as_active_blocker = not _is_closed_monitoring_row(row)
        blocker_status = "ACTIVE_BLOCKER" if counts_as_active_blocker else "CLOSED_RECOMPUTE_MONITORING"

        mappings.append(
            {
                "blocker_class": row["blocker_class"],
                "blocker_status": blocker_status,
                "counts_as_active_blocker": counts_as_active_blocker,
                "domain": row["domain"],
                "row_id": row["row_id"],
                "owning_lane": row["lane"],
                "required_closure_artifact": row["primary_artifact"],
                "required_evidence_surface": owner_row.get("required_evidence_surface", row["primary_target"]),
                "exit_criterion": owner_row.get("exit_criterion", "UNSPECIFIED"),
                "closure_gate": row["primary_gate"],
                "governance_checkpoint_status": row["governance_checkpoint_status"],
                "physics_checkpoint_status": row["physics_checkpoint_status"],
                "gate_runtime_status": row["gate_runtime_status"],
            }
        )

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "sources": {
            "completion_matrix": str(COMPLETION_MATRIX_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "closure_owner_map": str(CLOSURE_OWNER_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "rows_total": len(mappings),
        "active_rows_total": sum(1 for mapping in mappings if mapping["counts_as_active_blocker"]),
        "missing_owner_rows": sorted(missing_owner_rows),
        "mappings": mappings,
        "non_claim_boundary": "This blocker-to-closure map is a repository-local governance control artifact and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate blocker-to-closure map for audit packet linkage.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json",
        help="Output path for blocker-to-closure map JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override (e.g. 2026-04-10T00:00:00Z).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_blocker_closure_map(output_path=output_path, captured_at_utc=ns.captured_at_utc)
    print(
        "governance_blocker_closure_map_generate: "
        f"rows_total={payload['rows_total']} "
        f"missing_owner_rows={len(payload['missing_owner_rows'])} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
