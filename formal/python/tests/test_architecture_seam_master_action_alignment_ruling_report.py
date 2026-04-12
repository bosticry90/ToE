from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import architecture_seam_master_action_alignment_ruling_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_ruling_exhausted_when_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING_20260411_v0.json"
    )
    reports = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "architecture_seam_master_action_alignment_packet_execution": "formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_20260411_v0.json",
                "architecture_seam_master_action_alignment_packet_execution_report": "formal/output/reports/architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
            },
            "ruling_policy": {
                "next_action_if_exhausted": "REVIEW_POST_ARCHITECTURE_ALIGNMENT_DECISION_AND_DO_NOT_LOOP_ALIGNMENT_PACKET"
            },
        },
    )

    _write_json(
        tmp_path / "formal" / "docs" / "release" / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_20260411_v0.json",
        {"schema_id": "x"},
    )
    _write_json(
        reports / "architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
        {
            "summary": {
                "execution_classification": "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
                "bridge_object_materialized": True,
                "alignment_witness_bound": True,
                "target_row_recompute_triggered": True,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["alignment_ruling"] == "EXHAUSTED_UNDER_CURRENT_FILTER"
