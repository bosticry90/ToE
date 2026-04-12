from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_robustness_gap_review_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_execution_20260412_v0.json",
                "bridge_robustness_gap_review_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_ruling_20260412_v0.json",
                "bridge_probe_readiness_robustness_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_20260412_v0.json",
            },
            "refinement_spec": {
                "seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "refinement_focus": "THRESHOLD_STRICTNESS_ONLY",
                "pre_refinement_probe_ready_margin_min": 0.06,
                "refined_probe_ready_margin_min": 0.04,
                "path_falsification_observed": False,
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                    "ROBUSTNESS_REFINEMENT_INCONCLUSIVE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_REFINEMENT_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_ONLY",
            },
        },
    )


def _seed_common(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED",
                "gap_primary_cause": "THRESHOLD_STRICTNESS",
            },
            "objective_quality": {
                "inputs": {
                    "threshold_strictness_indicator": 0.02,
                    "fragility_indicator": 0.04,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_ruling_20260412_v0.json",
        {"summary": {"ruling_status": "TERMINAL_OUTCOME_CONFIRMED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "perturbed_signal_margin": 0.04,
            }
        },
    )


def test_refinement_execution_reports_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PROBE_READY"


def test_refinement_execution_reports_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "perturbed_signal_margin": 0.025,
            }
        },
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"


def test_refinement_execution_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["refinement_spec"]["path_falsification_observed"] = True
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PATH_FALSIFIED"


def test_refinement_execution_reports_inconclusive_when_gap_not_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "COMPARATOR_BOUND_HOLD_RETAINED",
                "gap_primary_cause": "SIGNAL_FRAGILITY",
            },
            "objective_quality": {"inputs": {"threshold_strictness_indicator": 0.01, "fragility_indicator": 0.07}},
        },
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ROBUSTNESS_REFINEMENT_INCONCLUSIVE"
