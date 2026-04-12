from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_probe_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_robustness_refinement_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json",
                "bridge_robustness_refinement_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_robustness_refinement_ruling_20260412_v0.json",
            },
            "probe_spec": {
                "seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "probe_signal_strength": 0.11,
                "probe_signal_threshold": 0.07,
                "probe_discrimination_threshold": 0.02,
                "path_falsification_observed": False,
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "PROBE_SIGNAL_CONFIRMED",
                    "PROBE_SIGNAL_NONDISCRIMINATIVE",
                    "PROBE_SIGNAL_INCONCLUSIVE",
                    "PROBE_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_PROBE_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_PROBE_EXECUTION_ONLY",
            },
        },
    )


def _seed_common(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SIGNAL_PROBE_READY",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_ruling_20260412_v0.json",
        {"summary": {"ruling_status": "TERMINAL_OUTCOME_CONFIRMED"}},
    )


def test_probe_execution_reports_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_SIGNAL_CONFIRMED"


def test_probe_execution_reports_nondiscriminative(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["probe_spec"]["probe_signal_strength"] = 0.08
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_SIGNAL_NONDISCRIMINATIVE"


def test_probe_execution_reports_inconclusive(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "ROBUSTNESS_REFINEMENT_INCONCLUSIVE",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            }
        },
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_SIGNAL_INCONCLUSIVE"


def test_probe_execution_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["probe_spec"]["path_falsification_observed"] = True
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_PATH_FALSIFIED"
