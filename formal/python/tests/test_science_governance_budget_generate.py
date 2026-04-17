from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_governance_budget_generate as tool


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_science_governance_budget_report_couples_ratio_to_dashboard(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "DASHBOARD_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json")
    monkeypatch.setattr(tool, "SCIENTIFIC_CORE_INDEX_PATH", tmp_path / "formal" / "docs" / "paper" / "SCIENTIFIC_CORE_INDEX_v0.md")
    monkeypatch.setattr(tool, "PHYSICS_FIRST_RULE_PATH", tmp_path / "formal" / "docs" / "release" / "PHYSICS_FIRST_EXECUTION_RULE_v0.md")
    monkeypatch.setattr(tool, "THROUGHPUT_PROGRAM_PATH", tmp_path / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md")

    _write_json(tool.DASHBOARD_REPORT_PATH, {"blocker_scoreboard": {"movement_status": "FLAT", "net_delta": 0, "exception_required": True}, "source_freshness": {"stale_input_warning": True}})
    _write_text(tool.SCIENTIFIC_CORE_INDEX_PATH, "| `SCI-0001` | x | y | z | n |\n| `SCI-0002` | x | y | z | n |\n| `CTL-0001` | x | y | z | n |\n")
    _write_text(tool.PHYSICS_FIRST_RULE_PATH, "## Core Rule\n- `math_strengthening`\n\n## Support Work Classification\n- `mirror_generation`\n")
    _write_text(tool.THROUGHPUT_PROGRAM_PATH, "- `PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE3_T05_THEOREM_DEPTH_ACCELERATION_BOOTSTRAP`\n")

    report = tool.build_budget_report(output_path=tmp_path / "out.json", captured_at_utc="2026-04-16T00:00:00Z")
    assert report["representative_surface_counts"]["science_core_rows"] == 2
    assert report["representative_surface_counts"]["governance_control_rows"] == 1
    assert report["dashboard_coupling"]["exception_required"] is True
    assert report["budget_posture"]["budget_posture"] == "SCIENCE_REBALANCE_REVIEW_REQUIRED"


def test_science_governance_budget_report_flags_control_heavy_when_ratio_low(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "DASHBOARD_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json")
    monkeypatch.setattr(tool, "SCIENTIFIC_CORE_INDEX_PATH", tmp_path / "formal" / "docs" / "paper" / "SCIENTIFIC_CORE_INDEX_v0.md")
    monkeypatch.setattr(tool, "PHYSICS_FIRST_RULE_PATH", tmp_path / "formal" / "docs" / "release" / "PHYSICS_FIRST_EXECUTION_RULE_v0.md")
    monkeypatch.setattr(tool, "THROUGHPUT_PROGRAM_PATH", tmp_path / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md")

    _write_json(tool.DASHBOARD_REPORT_PATH, {"blocker_scoreboard": {"movement_status": "INCREASING", "net_delta": 1, "exception_required": True}, "source_freshness": {"stale_input_warning": False}})
    _write_text(tool.SCIENTIFIC_CORE_INDEX_PATH, "| `SCI-0001` | x | y | z | n |\n| `CTL-0001` | x | y | z | n |\n| `CTL-0002` | x | y | z | n |\n")
    _write_text(tool.PHYSICS_FIRST_RULE_PATH, "## Core Rule\n- `math_strengthening`\n\n## Support Work Classification\n- `mirror_generation`\n")
    _write_text(tool.THROUGHPUT_PROGRAM_PATH, "- `PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE4_T06_SEAM_EMPIRICAL_THROUGHPUT_BOOTSTRAP`\n")

    report = tool.build_budget_report(output_path=tmp_path / "out.json", captured_at_utc=None)
    assert report["budget_posture"]["budget_posture"] == "CONTROL_HEAVY_REBALANCE_REQUIRED"