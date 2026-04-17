from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_computational_analysis_packet_01_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_build_report_forces_packet_decision_inconclusive(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    packet_path = tmp_path / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
    first_test_packet_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json"
    )
    signal_interpretation_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json"
    )
    comparator_binding_ruling_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_ruling_20260412_v0.json"
    )
    probe_ruling_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json"
    )

    _write_json(
        packet_path,
        {
            "artifact_id": "qm_stat_rl10_computational_analysis_packet_01_v0",
            "payload": {
                "status": "RUN_BOUNDED_v0_NONCLAIM",
                "decision": "INCONCLUSIVE_v0",
            },
        },
    )
    _write_json(
        first_test_packet_report_path,
        {
            "criteria": {
                "transition_structure_coherent": True,
                "bridge_observable_ready": True,
                "governance_boundary_preserved": True,
            },
            "summary": {"terminal_outcome": "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE"},
        },
    )
    _write_json(
        signal_interpretation_report_path,
        {"summary": {"interpretation_outcome": "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE"}},
    )
    _write_json(
        comparator_binding_ruling_report_path,
        {"summary": {"terminal_outcome": "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"}},
    )
    _write_json(
        probe_ruling_report_path,
        {"summary": {"terminal_outcome": "PROBE_SIGNAL_CONFIRMED"}},
    )

    report = tool.build_report(
        packet_path=packet_path,
        first_test_packet_report_path=first_test_packet_report_path,
        signal_interpretation_report_path=signal_interpretation_report_path,
        comparator_binding_ruling_report_path=comparator_binding_ruling_report_path,
        probe_ruling_report_path=probe_ruling_report_path,
        captured_at_utc=None,
    )

    assert report["summary"]["packet_decision"] == "INCONCLUSIVE_v0"
    assert report["summary"]["stability_classification"] == "STABLE_v0"
    assert report["summary"]["comparator_classification"] == "COMPARATOR_SENSITIVE_v0"
    assert report["summary"]["discriminator_classification"] == "DISCRIMINATIVE_v0"
    assert report["summary"]["subordinate_disposition"] == "RETAIN_v0"


def test_build_report_prunes_when_bridge_unstable(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    packet_path = tmp_path / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
    first_test_packet_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json"
    )
    signal_interpretation_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json"
    )
    comparator_binding_ruling_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_ruling_20260412_v0.json"
    )
    probe_ruling_report_path = (
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json"
    )

    _write_json(packet_path, {"artifact_id": "qm_stat_rl10_computational_analysis_packet_01_v0", "payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "INCONCLUSIVE_v0"}})
    _write_json(first_test_packet_report_path, {"criteria": {"transition_structure_coherent": False, "bridge_observable_ready": False, "governance_boundary_preserved": True}, "summary": {"terminal_outcome": "BRIDGE_SEAM_INTERNAL_ONLY"}})
    _write_json(signal_interpretation_report_path, {"summary": {"interpretation_outcome": "BRIDGE_SIGNAL_INTERNAL_ONLY"}})
    _write_json(comparator_binding_ruling_report_path, {"summary": {"terminal_outcome": "COMPARATOR_BINDING_PARTIAL_HOLD"}})
    _write_json(probe_ruling_report_path, {"summary": {"terminal_outcome": "PROBE_SIGNAL_INCONCLUSIVE"}})

    report = tool.build_report(
        packet_path=packet_path,
        first_test_packet_report_path=first_test_packet_report_path,
        signal_interpretation_report_path=signal_interpretation_report_path,
        comparator_binding_ruling_report_path=comparator_binding_ruling_report_path,
        probe_ruling_report_path=probe_ruling_report_path,
        captured_at_utc=None,
    )

    assert report["summary"]["packet_decision"] == "INCONCLUSIVE_v0"
    assert report["summary"]["stability_classification"] == "UNSTABLE_v0"
    assert report["summary"]["subordinate_disposition"] == "PRUNE_v0"