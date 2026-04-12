from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_probe_readiness_robustness_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_20260412_v0.json",
                "bridge_probe_readiness_robustness_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_ruling_20260412_v0.json",
                "bridge_external_comparator_binding_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
            },
            "gap_review_spec": {
                "review_axes": [
                    "THRESHOLD_STRICTNESS",
                    "SIGNAL_FRAGILITY",
                    "UNDERDECLARED_BRIDGE_STRUCTURE",
                    "COMPARATOR_BINDING_LIMITS",
                ],
                "threshold_strictness_indicator": 0.02,
                "fragility_indicator": 0.04,
                "underdeclared_structure_detected": False,
                "comparator_binding_limit_detected": False,
                "path_falsification_observed": False,
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED",
                    "COMPARATOR_BOUND_HOLD_RETAINED",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                    "PROBE_READINESS_CRITERIA_REQUIRE_REVISION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_ROBUSTNESS_GAP_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_ROBUSTNESS_GAP_REVIEW_ONLY",
            },
        },
    )


def _seed_common(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_ruling_20260412_v0.json",
        {
            "summary": {
                "ruling_status": "TERMINAL_OUTCOME_CONFIRMED",
                "terminal_outcome": "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"}},
    )


def test_gap_review_reports_refinement_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED"


def test_gap_review_reports_hold_retained(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["gap_review_spec"]["threshold_strictness_indicator"] = 0.01
    declaration["gap_review_spec"]["fragility_indicator"] = 0.06
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "COMPARATOR_BOUND_HOLD_RETAINED"


def test_gap_review_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["gap_review_spec"]["path_falsification_observed"] = True
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PATH_FALSIFIED"


def test_gap_review_reports_criteria_revision(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["gap_review_spec"]["comparator_binding_limit_detected"] = True
    declaration["gap_review_spec"]["threshold_strictness_indicator"] = 0.04
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_CRITERIA_REQUIRE_REVISION"