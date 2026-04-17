from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_computational_analysis_packet_01_refinement_01_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_build_report_retains_under_tightened_margin(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    refinement_path = tmp_path / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_refinement_01_v0.json"
    baseline_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json"
    signal_interpretation_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json"
    probe_ruling_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json"

    _write_json(refinement_path, {"payload": {"authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS", "decision": "INCONCLUSIVE_v0", "refinement_sequence": 1, "max_refinements_authorized": 1, "packet02_authorized": False, "restart_implication": False, "blocker_movement_claim": False, "baseline_value": 0.0, "refined_value": 0.06, "variation_id": "COMPARATOR_MARGIN_TIGHTENING_v0", "variation_axis": "COMPARATOR_SENSITIVITY_MARGIN_FLOOR"}})
    _write_json(baseline_report_path, {"criteria": {"packet_decision_forced_inconclusive": True}, "classificatory_findings": {"stability_classification": "STABLE_v0"}})
    _write_json(signal_interpretation_report_path, {"objective_quality": {"inputs": {"signal_margin": 0.07}}})
    _write_json(probe_ruling_report_path, {"summary": {"terminal_outcome": "PROBE_SIGNAL_CONFIRMED"}})

    report = tool.build_report(refinement_path=refinement_path, baseline_report_path=baseline_report_path, signal_interpretation_report_path=signal_interpretation_report_path, probe_ruling_report_path=probe_ruling_report_path, captured_at_utc=None)
    assert report["summary"]["packet_decision"] == "INCONCLUSIVE_v0"
    assert report["summary"]["comparator_classification"] == "COMPARATOR_SENSITIVE_v0"
    assert report["summary"]["subordinate_disposition"] == "RETAIN_v0"


def test_build_report_inconclusive_when_margin_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    refinement_path = tmp_path / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_refinement_01_v0.json"
    baseline_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json"
    signal_interpretation_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json"
    probe_ruling_report_path = tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json"

    _write_json(refinement_path, {"payload": {"authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS", "decision": "INCONCLUSIVE_v0", "refinement_sequence": 1, "max_refinements_authorized": 1, "packet02_authorized": False, "restart_implication": False, "blocker_movement_claim": False, "baseline_value": 0.0, "refined_value": 0.09, "variation_id": "COMPARATOR_MARGIN_TIGHTENING_v0", "variation_axis": "COMPARATOR_SENSITIVITY_MARGIN_FLOOR"}})
    _write_json(baseline_report_path, {"criteria": {"packet_decision_forced_inconclusive": True}, "classificatory_findings": {"stability_classification": "STABLE_v0"}})
    _write_json(signal_interpretation_report_path, {"objective_quality": {"inputs": {"signal_margin": 0.07}}})
    _write_json(probe_ruling_report_path, {"summary": {"terminal_outcome": "PROBE_SIGNAL_CONFIRMED"}})

    report = tool.build_report(refinement_path=refinement_path, baseline_report_path=baseline_report_path, signal_interpretation_report_path=signal_interpretation_report_path, probe_ruling_report_path=probe_ruling_report_path, captured_at_utc=None)
    assert report["summary"]["comparator_classification"] == "COMPARATOR_INSENSITIVE_v0"
    assert report["summary"]["subordinate_disposition"] == "INCONCLUSIVE_v0"
