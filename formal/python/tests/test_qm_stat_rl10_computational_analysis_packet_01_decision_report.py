from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_computational_analysis_packet_01_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_build_report_refines_when_signal_is_meaningful(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    packet_path = tmp_path / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
    executed_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json"

    _write_json(packet_path, {"payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "INCONCLUSIVE_v0"}})
    _write_json(
        executed_report_path,
        {
            "criteria": {"packet_decision_forced_inconclusive": True, "restart_semantics_preserved": True},
            "classificatory_findings": {
                "stability_classification": "STABLE_v0",
                "comparator_classification": "COMPARATOR_SENSITIVE_v0",
                "discriminator_classification": "DISCRIMINATIVE_v0",
                "subordinate_disposition": "RETAIN_v0",
            },
            "summary": {"packet_decision": "INCONCLUSIVE_v0"},
        },
    )

    report = tool.build_report(packet_path=packet_path, executed_report_path=executed_report_path, captured_at_utc=None)
    assert report["summary"]["decision"] == "REFINE_v0"
    assert report["criteria"]["packet02_authorized"] is False
    assert report["criteria"]["restart_implication"] is False


def test_build_report_retires_when_boundary_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    packet_path = tmp_path / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
    executed_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json"

    _write_json(packet_path, {"payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "RETAIN_v0"}})
    _write_json(
        executed_report_path,
        {
            "criteria": {"packet_decision_forced_inconclusive": False, "restart_semantics_preserved": True},
            "classificatory_findings": {
                "stability_classification": "UNSTABLE_v0",
                "comparator_classification": "COMPARATOR_INSENSITIVE_v0",
                "discriminator_classification": "NONDISCRIMINATIVE_v0",
                "subordinate_disposition": "PRUNE_v0",
            },
            "summary": {"packet_decision": "RETAIN_v0"},
        },
    )

    report = tool.build_report(packet_path=packet_path, executed_report_path=executed_report_path, captured_at_utc=None)
    assert report["summary"]["decision"] == "RETIRE_v0"
