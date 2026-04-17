from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_computational_analysis_packet_01_refinement_closeout_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_build_report_retain_refinement_when_signal_persists(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    baseline_decision_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_decision_20260416_v0.json"
    refinement_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_refinement_01_20260416_v0.json"

    _write_json(baseline_decision_path, {"summary": {"decision": "REFINE_v0", "authorized_follow_on": "ONE_BOUNDED_PACKET01_REFINEMENT_ONLY"}})
    _write_json(refinement_report_path, {"criteria": {"same_auxiliary_authorization_class": True, "same_packet_level_inconclusive_ceiling": True, "one_refinement_only": True, "packet02_authorized": False, "restart_implication": False, "blocker_movement_claim": False}, "summary": {"stability_classification": "STABLE_v0", "comparator_classification": "COMPARATOR_SENSITIVE_v0", "discriminator_classification": "DISCRIMINATIVE_v0", "subordinate_disposition": "RETAIN_v0"}})

    report = tool.build_report(baseline_decision_path=baseline_decision_path, refinement_report_path=refinement_report_path, captured_at_utc=None)
    assert report["summary"]["decision"] == "RETAIN_REFINEMENT_v0"
    assert report["summary"]["authorized_follow_on"] == "NONE"


def test_build_report_stop_family_when_not_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    baseline_decision_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_decision_20260416_v0.json"
    refinement_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_refinement_01_20260416_v0.json"

    _write_json(baseline_decision_path, {"summary": {"decision": "RETAIN_v0", "authorized_follow_on": "NONE"}})
    _write_json(refinement_report_path, {"criteria": {"same_auxiliary_authorization_class": True, "same_packet_level_inconclusive_ceiling": True, "one_refinement_only": True, "packet02_authorized": False, "restart_implication": False, "blocker_movement_claim": False}, "summary": {"stability_classification": "STABLE_v0", "comparator_classification": "COMPARATOR_SENSITIVE_v0", "discriminator_classification": "DISCRIMINATIVE_v0", "subordinate_disposition": "RETAIN_v0"}})

    report = tool.build_report(baseline_decision_path=baseline_decision_path, refinement_report_path=refinement_report_path, captured_at_utc=None)
    assert report["summary"]["decision"] == "STOP_PACKET01_FAMILY_v0"
