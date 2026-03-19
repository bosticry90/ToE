from __future__ import annotations

import argparse
import hashlib
import json
import sqlite3
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "TOE_SQL_INTEGRITY_SNAPSHOT_REPORT_v0"


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def build_snapshot(*, db_path: Path, report_path: Path) -> dict[str, Any]:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)

    schema_path = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"
    matrix_path = REPO_ROOT / "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json"
    phase_registry_path = REPO_ROOT / "formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"

    matrix = _load_json(matrix_path)
    phase_registry = _load_json(phase_registry_path)

    pillar_rows = matrix.get("pillars", {})
    if not isinstance(pillar_rows, dict):
        raise ValueError("PILLAR_STATUS_MATRIX_v1.json must contain object key 'pillars'.")

    registry_entries = phase_registry.get("pillars", [])
    if not isinstance(registry_entries, list):
        raise ValueError("PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json must contain list key 'pillars'.")

    conn = sqlite3.connect(str(db_path))
    try:
        cur = conn.cursor()
        cur.execute("DROP TABLE IF EXISTS artifacts")
        cur.execute("DROP TABLE IF EXISTS matrix_pillars")
        cur.execute("DROP TABLE IF EXISTS phase_registry")

        cur.execute(
            """
            CREATE TABLE artifacts (
                artifact_path TEXT PRIMARY KEY,
                sha256 TEXT NOT NULL,
                size_bytes INTEGER NOT NULL
            )
            """
        )
        cur.execute(
            """
            CREATE TABLE matrix_pillars (
                pillar_id TEXT PRIMARY KEY,
                matrix_status TEXT,
                full_derivation_adjudication TEXT,
                inevitability_adjudication TEXT
            )
            """
        )
        cur.execute(
            """
            CREATE TABLE phase_registry (
                pillar_id TEXT PRIMARY KEY,
                mode TEXT NOT NULL,
                authority_doc_path TEXT
            )
            """
        )

        for path in (schema_path, matrix_path, phase_registry_path):
            data = path.read_bytes()
            cur.execute(
                "INSERT INTO artifacts (artifact_path, sha256, size_bytes) VALUES (?, ?, ?)",
                (str(path.relative_to(REPO_ROOT)).replace("\\", "/"), _sha256_bytes(data), len(data)),
            )

        for pillar_id, row in sorted(pillar_rows.items()):
            if not isinstance(row, dict):
                continue
            cur.execute(
                """
                INSERT INTO matrix_pillars (
                    pillar_id,
                    matrix_status,
                    full_derivation_adjudication,
                    inevitability_adjudication
                ) VALUES (?, ?, ?, ?)
                """,
                (
                    pillar_id,
                    row.get("matrix_status"),
                    row.get("full_derivation_adjudication"),
                    row.get("inevitability_adjudication"),
                ),
            )

        for entry in registry_entries:
            if not isinstance(entry, dict):
                continue
            pillar_id = str(entry.get("pillar_id", "")).strip()
            if not pillar_id:
                continue
            cur.execute(
                "INSERT INTO phase_registry (pillar_id, mode, authority_doc_path) VALUES (?, ?, ?)",
                (pillar_id, str(entry.get("mode", "")), entry.get("authority_doc_path")),
            )

        conn.commit()

        cur.execute(
            """
            SELECT r.pillar_id
            FROM phase_registry r
            LEFT JOIN matrix_pillars m ON m.pillar_id = r.pillar_id
            WHERE m.pillar_id IS NULL
            ORDER BY r.pillar_id
            """
        )
        missing_matrix_rows = [row[0] for row in cur.fetchall()]

        cur.execute("SELECT COUNT(*) FROM matrix_pillars")
        matrix_count = int(cur.fetchone()[0])

        cur.execute("SELECT COUNT(*) FROM phase_registry")
        registry_count = int(cur.fetchone()[0])

    finally:
        conn.close()

    issues: list[str] = []
    if missing_matrix_rows:
        issues.append("phase_registry_missing_matrix_rows:" + ",".join(missing_matrix_rows))

    report = {
        "schema_id": SCHEMA_ID,
        "generated_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "db_path": str(db_path),
        "artifact_count": 3,
        "matrix_pillar_count": matrix_count,
        "phase_registry_count": registry_count,
        "issues": issues,
        "mirror_only": True,
    }

    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a local SQL mirror snapshot for integrity checks.")
    parser.add_argument(
        "--db",
        type=Path,
        default=REPO_ROOT / "formal/output/reports/toe_integrity_snapshot_v0.sqlite3",
        help="Output sqlite3 database path.",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=REPO_ROOT / "formal/output/reports/toe_integrity_snapshot_report_v0.json",
        help="Output JSON report path.",
    )
    parser.add_argument("--fail-on-issues", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    db_path = (REPO_ROOT / ns.db).resolve() if not ns.db.is_absolute() else ns.db
    report_path = (REPO_ROOT / ns.report).resolve() if not ns.report.is_absolute() else ns.report

    report = build_snapshot(db_path=db_path, report_path=report_path)
    print(f"sql_integrity_snapshot: issues={len(report['issues'])} report_path={report_path}")

    if report["issues"] and ns.fail_on_issues:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
