from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_restart_mode_selection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    selected_restart_mode: str = "NEW_POLICY_EVIDENCE_STANDARD_LANE",
    untouched_lane_candidate_id: str = "UNSET",
    untouched_lane_non_consumption_proof_declared: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_common_failure_modes_synthesis_report": "formal/output/reports/science_common_failure_modes_synthesis_20260412_v0.json",
                "probe_readiness_standard_candidate_report": "formal/output/reports/probe_readiness_standard_candidate_20260412_v0.json",
            },
            "selection_policy": {
                "required_synthesis_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
                "allowed_probe_standard_outcomes": [
                    "REQUIRES_RESTART_SELECTION_LAYER",
                    "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED",
                ],
                "allowed_restart_modes": [
                    "NEW_POLICY_EVIDENCE_STANDARD_LANE",
                    "GENUINELY_UNTOUCHED_LANE",
                ],
                "selected_restart_mode": selected_restart_mode,
                "policy_lane_id": "POLICY-PROBE-READINESS-v1",
                "untouched_lane_candidate_id": untouched_lane_candidate_id,
                "untouched_lane_non_consumption_proof_declared": untouched_lane_non_consumption_proof_declared,
                "consumed_lane_aliases": [
                    "QM-STAT",
                    "GR-ROW-001",
                    "EM-QFT",
                    "SHARED-MODEL-CLASS",
                    "QFT-GR",
                ],
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "selection_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_RESTART_MODE_SELECTION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_RESTART_MODE_SELECTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "RESTART_MODE_SELECTED_POLICY_LANE",
                    "RESTART_MODE_SELECTED_UNTOUCHED_LANE",
                    "RESTART_MODE_SELECTION_BLOCKED_CONSUMED_LANE_ALIAS",
                    "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    synthesis_outcome: str = "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_common_failure_modes_synthesis_20260412_v0.json",
        {"summary": {"terminal_outcome": synthesis_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "probe_readiness_standard_candidate_20260412_v0.json",
        {"summary": {"terminal_outcome": "REQUIRES_RESTART_SELECTION_LAYER"}},
    )


def test_reports_restart_mode_selected_policy_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_MODE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, selected_restart_mode="NEW_POLICY_EVIDENCE_STANDARD_LANE")
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESTART_MODE_SELECTED_POLICY_LANE"


def test_reports_restart_mode_selected_untouched_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_MODE_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        selected_restart_mode="GENUINELY_UNTOUCHED_LANE",
        untouched_lane_candidate_id="NEUTRINO-BRIDGE-EXPLORATORY",
        untouched_lane_non_consumption_proof_declared=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESTART_MODE_SELECTED_UNTOUCHED_LANE"


def test_reports_restart_mode_selection_blocked_consumed_lane_alias(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_MODE_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        selected_restart_mode="GENUINELY_UNTOUCHED_LANE",
        untouched_lane_candidate_id="QFT-GR",
        untouched_lane_non_consumption_proof_declared=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESTART_MODE_SELECTION_BLOCKED_CONSUMED_LANE_ALIAS"


def test_reports_restart_mode_selection_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_MODE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, synthesis_outcome="COMMON_FAILURE_MODES_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE"
