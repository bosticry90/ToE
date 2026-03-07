from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.sql_integrity_snapshot import SCHEMA_ID
from formal.python.tools.sql_integrity_snapshot import build_snapshot


def test_sql_integrity_snapshot_writes_db_and_report(tmp_path: Path) -> None:
    db_path = tmp_path / "snapshot.sqlite3"
    report_path = tmp_path / "snapshot_report.json"

    report = build_snapshot(db_path=db_path, report_path=report_path)

    assert db_path.exists()
    assert report_path.exists()
    assert report["schema_id"] == SCHEMA_ID
    assert report["mirror_only"] is True

    payload = json.loads(report_path.read_text(encoding="utf-8"))
    assert payload["schema_id"] == SCHEMA_ID
    assert "issues" in payload
