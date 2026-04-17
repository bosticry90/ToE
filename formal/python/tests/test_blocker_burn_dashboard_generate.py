from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import blocker_burn_dashboard_generate as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_blocker_burn_dashboard_materializes_expected_sections(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "COMPLETION_MATRIX_PATH", tmp_path / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md")
    monkeypatch.setattr(tool, "TREND_WINDOW_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json")
    monkeypatch.setattr(tool, "CLOSURE_MAP_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json")
    monkeypatch.setattr(tool, "LEDGER_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json")
    monkeypatch.setattr(tool, "BASELINE_PACK_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "convergence_baseline_pack_20260409_v0.json")

    blocker_review_path = tmp_path / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json"
    _write_json(
        blocker_review_path,
        {
            "row_promotion_count": 0,
            "next_action": "EXECUTE_TGC77_AND_TGC78_BEFORE_RESUMING_REPEATING_CADENCE",
        },
    )

    _write_text(
        tool.COMPLETION_MATRIX_PATH,
        """# TOE Global Completion Matrix v0\n\n## Status\n- ACTIVE\n- Date: 2026-04-08\n\n## Completion rows\n| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n| ROW-SEAM-QM-STAT-001 | seam | QM_STAT_CYCLE11 | NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED | SEAM_INTEGRATION_GAP | formal/docs/paper/a.md | formal/output/a.json | formal/python/tests/test_a.py |\n| ROW-PILLAR-QM-001 | pillar | QM_DERIVATION_CHAIN | THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | formal/docs/paper/b.md | formal/output/b.json | formal/python/tests/test_b.py |\n""",
    )
    _write_json(
        tool.TREND_WINDOW_REPORT_PATH,
        {
            "captured_at_utc": "2026-04-10T00:00:00Z",
            "window": {"start": "TGC-69", "end": "TGC-76"},
            "tranche_id": "TGC-76",
            "blocker_counts": {
                "prior": {
                    "THEOREM_GAP": 7,
                    "SEAM_INTEGRATION_GAP": 3,
                    "PARITY_DRIFT": 1,
                    "GOVERNANCE_GUARDRAIL": 0,
                    "EVIDENCE_ALIGNMENT_GAP": 0,
                },
                "current": {
                    "THEOREM_GAP": 6,
                    "SEAM_INTEGRATION_GAP": 3,
                    "PARITY_DRIFT": 1,
                    "GOVERNANCE_GUARDRAIL": 0,
                    "EVIDENCE_ALIGNMENT_GAP": 0,
                },
                "net_delta": -1,
            },
            "exception_requirement": {
                "exception_required": False,
                "exception_artifact_pointer": None,
            },
        },
    )
    _write_json(
        tool.CLOSURE_MAP_REPORT_PATH,
        {
            "captured_at_utc": "2026-04-10T00:00:00Z",
            "rows_total": 2,
            "missing_owner_rows": [],
            "mappings": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                    "exit_criterion": "EXIT_A",
                    "closure_gate": "formal/python/tests/test_a.py",
                    "required_closure_artifact": "formal/output/a.json",
                },
                {
                    "row_id": "ROW-PILLAR-QM-001",
                    "blocker_class": "THEOREM_GAP",
                    "exit_criterion": "EXIT_B",
                    "closure_gate": "formal/python/tests/test_b.py",
                    "required_closure_artifact": "formal/output/b.json",
                },
            ],
        },
    )
    _write_json(
        tool.LEDGER_REPORT_PATH,
        {
            "captured_at_utc": "2026-04-11T00:00:00Z",
            "progress_classification": "PROGRESS",
            "actual_blocker_state_change": "NEGATIVE_DELTA_DETECTED",
        },
    )
    _write_json(
        tool.BASELINE_PACK_REPORT_PATH,
        {
            "captured_at_utc": "2026-04-09T00:00:00Z",
            "required_metrics": {
                "blocker_count_by_class": {
                    "current": {
                        "THEOREM_GAP": 7,
                        "SEAM_INTEGRATION_GAP": 3,
                        "PARITY_DRIFT": 1,
                        "GOVERNANCE_GUARDRAIL": 0,
                        "EVIDENCE_ALIGNMENT_GAP": 0,
                    }
                }
            },
        },
    )

    for relpath in [
        "formal/docs/paper/a.md",
        "formal/docs/paper/b.md",
        "formal/output/a.json",
        "formal/output/b.json",
        "formal/python/tests/test_a.py",
        "formal/python/tests/test_b.py",
    ]:
        _write_text(tmp_path / relpath, "placeholder\n")

    report = tool.build_dashboard(
        output_path=tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        captured_at_utc="2026-04-16T00:00:00Z",
    )

    assert report["schema_id"] == "BLOCKER_BURN_DASHBOARD_20260416_v0"
    assert report["blocker_scoreboard"]["net_delta"] == -1
    assert report["blocker_scoreboard"]["delta_by_class"]["THEOREM_GAP"] == -1
    assert report["row_blocker_contributions"]["blocker_classes"]["THEOREM_GAP"]["row_ids"] == ["ROW-PILLAR-QM-001"]
    assert report["row_promotion_readiness"]["rows_with_all_paths_pinned"] == 2
    assert report["tranche_timeline"]["ledger_progress_classification"] == "PROGRESS"
    assert report["source_freshness"]["stale_input_warning"] is True


def test_blocker_burn_dashboard_flags_missing_paths_in_readiness(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "COMPLETION_MATRIX_PATH", tmp_path / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md")
    monkeypatch.setattr(tool, "TREND_WINDOW_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json")
    monkeypatch.setattr(tool, "CLOSURE_MAP_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json")
    monkeypatch.setattr(tool, "LEDGER_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json")
    monkeypatch.setattr(tool, "BASELINE_PACK_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "convergence_baseline_pack_20260409_v0.json")

    _write_json(tmp_path / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json", {"row_promotion_count": 0, "next_action": "NEXT"})
    _write_text(
        tool.COMPLETION_MATRIX_PATH,
        """# TOE Global Completion Matrix v0\n\n## Status\n- Date: 2026-04-08\n\n## Completion rows\n| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n| ROW-PILLAR-GR-001 | pillar | GR_DERIVATION_CHAIN | SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | formal/docs/paper/missing.md | formal/output/missing.json | formal/python/tests/test_missing.py |\n""",
    )
    _write_json(tool.TREND_WINDOW_REPORT_PATH, {"captured_at_utc": "2026-04-10T00:00:00Z", "window": {}, "tranche_id": "TGC-76", "blocker_counts": {"prior": {}, "current": {}, "net_delta": 0}, "exception_requirement": {"exception_required": True, "exception_artifact_pointer": "formal/output/ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json"}})
    _write_json(tool.CLOSURE_MAP_REPORT_PATH, {"captured_at_utc": "2026-04-10T00:00:00Z", "rows_total": 1, "missing_owner_rows": ["ROW-PILLAR-GR-001"], "mappings": []})
    _write_json(tool.LEDGER_REPORT_PATH, {"captured_at_utc": "2026-04-11T00:00:00Z", "progress_classification": "MAINTENANCE", "actual_blocker_state_change": "NO_DELTA_DETECTED_ROUTE_TO_REWORK"})
    _write_json(tool.BASELINE_PACK_REPORT_PATH, {"captured_at_utc": "2026-04-09T00:00:00Z", "required_metrics": {}})

    report = tool.build_dashboard(output_path=tmp_path / "out.json", captured_at_utc=None)
    row = report["row_promotion_readiness"]["rows"][0]
    assert row["promotion_readiness_status"] == "BLOCKED_MISSING_CANONICAL_PATH"
    assert report["blocker_scoreboard"]["exception_required"] is True