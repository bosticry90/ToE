from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_probe_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
                "bridge_probe_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "significance_policy": {
                "external_path_success_signal_margin_min": 0.05,
                "confirmed_but_limited_signal_margin_min": 0.02,
                "one_more_cycle_signal_margin_min": 0.0,
                "comparator_repeatability_confirmed": False,
                "cross_probe_consistency_confirmed": False,
            },
            "adjudication_contract": {
                "allowed_outcomes": [
                    "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE",
                    "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
                    "PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE",
                    "PROBE_SIGNAL_PATH_HOLD",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_PROBE_SIGNIFICANCE_ADJUDICATION_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_ONLY",
                "default_outcome": "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    execution_outcome: str = "PROBE_SIGNAL_CONFIRMED",
    ruling_status: str = "TERMINAL_OUTCOME_CONFIRMED",
    ruling_outcome: str = "PROBE_SIGNAL_CONFIRMED",
    signal_margin: float = 0.04,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": execution_outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": signal_margin,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json",
        {
            "summary": {
                "ruling_status": ruling_status,
                "terminal_outcome": ruling_outcome,
            }
        },
    )


def test_probe_significance_reports_external_path_success_candidate(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, signal_margin=0.07)

    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["significance_policy"]["comparator_repeatability_confirmed"] = True
    declaration["significance_policy"]["cross_probe_consistency_confirmed"] = True
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["adjudication_outcome"] == "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE"


def test_probe_significance_reports_confirmed_but_limited(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, signal_margin=0.04)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["adjudication_outcome"] == "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED"


def test_probe_significance_reports_requires_one_more_cycle(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        execution_outcome="PROBE_SIGNAL_NONDISCRIMINATIVE",
        ruling_outcome="PROBE_SIGNAL_NONDISCRIMINATIVE",
        signal_margin=0.01,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["adjudication_outcome"]
        == "PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE"
    )


def test_probe_significance_reports_path_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        execution_outcome="PROBE_PATH_FALSIFIED",
        ruling_outcome="PROBE_PATH_FALSIFIED",
        signal_margin=-0.01,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["adjudication_outcome"] == "PROBE_SIGNAL_PATH_HOLD"
