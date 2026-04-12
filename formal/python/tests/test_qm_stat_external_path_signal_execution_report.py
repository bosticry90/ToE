from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_external_path_signal_execution_report as execution_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "qm_stat_external_path_signal_packet_report": "formal/output/reports/qm_stat_external_path_signal_packet_20260411_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
                "qm_stat_discovery_interpretation_report": "formal/output/reports/qm_stat_discovery_interpretation_report_20260411_v0.json",
                "qm_stat_discovery_numerical_probe_execution_report": "formal/output/reports/qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "EXTERNAL_PATH_SIGNAL_PRODUCED",
                    "PATH_FALSIFIED",
                    "INTERNAL_ONLY_REMAINS",
                ],
                "success_rule": "CURRENT_INTERPRETATION_IN_EXTERNALLY_COMPARABLE_OR_NUMERICAL_PROBE_READY_AND_BASELINE_COMPARATOR_EVALUABLE",
                "path_falsification_rule": "PATH_FALSIFICATION_OBSERVED_TRUE",
                "failure_rule": "COMPARATOR_DECLARED_BUT_NO_EXTERNAL_SEPARATION_BEYOND_INTERNAL_ONLY_STATE",
                "no_loop_rule": "ONE_QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_ONLY",
            },
        },
    )


def _write_common_inputs(reports_dir: Path) -> None:
    _write_json(
        reports_dir / "qm_stat_external_path_signal_packet_20260411_v0.json",
        {"summary": {"packet_outcome": "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED"}},
    )
    _write_json(
        reports_dir / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "candidate_mapping_status": "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY",
            }
        },
    )
    _write_json(
        reports_dir / "qm_stat_discovery_interpretation_report_20260411_v0.json",
        {"summary": {"interpretation": "INTERNAL_DISCRIMINATIVE_ONLY"}},
    )
    _write_json(
        reports_dir / "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
        {"summary": {"probe_signal": "PROBE_NONDISCRIMINATIVE", "path_falsification_observed": False}},
    )


def test_qm_stat_external_path_execution_reports_internal_only_remains(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(execution_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)

    report = execution_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["execution_outcome"] == "INTERNAL_ONLY_REMAINS"
    assert report["summary"]["classification_reason"] == "BASELINE_DECLARED_BUT_QM_STAT_NOT_YET_EXTERNALLY_COMPARABLE"


def test_qm_stat_external_path_execution_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(execution_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)
    _write_json(
        reports_dir / "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
        {"summary": {"probe_signal": "PROBE_PATH_FALSIFIED", "path_falsification_observed": True}},
    )

    report = execution_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["execution_outcome"] == "PATH_FALSIFIED"
    assert report["summary"]["next_action"] == "RETIRE_QM_STAT_EXTERNAL_PATH_CANDIDATE_AND_DO_NOT_LOOP"


def test_qm_stat_external_path_execution_reports_external_signal_when_mapping_is_ready(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(execution_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)
    _write_json(
        reports_dir / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "candidate_mapping_status": "BASELINE_COMPARATOR_EVALUABLE",
            }
        },
    )
    _write_json(
        reports_dir / "qm_stat_discovery_interpretation_report_20260411_v0.json",
        {"summary": {"interpretation": "EXTERNALLY_COMPARABLE"}},
    )

    report = execution_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["execution_outcome"] == "EXTERNAL_PATH_SIGNAL_PRODUCED"
    assert report["summary"]["next_action"] == "REOPEN_DISCOVERY_EXPANSION_REVIEW_ONCE"
