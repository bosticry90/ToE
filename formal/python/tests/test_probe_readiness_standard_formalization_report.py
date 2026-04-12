from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import probe_readiness_standard_formalization_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_common_failure_modes_synthesis_report": "formal/output/reports/science_common_failure_modes_synthesis_20260412_v0.json",
                "probe_readiness_standard_candidate_report": "formal/output/reports/probe_readiness_standard_candidate_20260412_v0.json",
                "science_restart_mode_selection_report": "formal/output/reports/science_restart_mode_selection_20260412_v0.json",
            },
            "formalization_policy": {
                "required_synthesis_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
                "allowed_candidate_outcomes": [
                    "REQUIRES_RESTART_SELECTION_LAYER",
                    "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED",
                ],
                "required_restart_selection_outcome": "RESTART_MODE_SELECTED_POLICY_LANE",
                "required_standard_keys": [
                    "comparator_fidelity_minimum",
                    "repeatability_stability_minimum",
                    "observable_mapping_minimum",
                    "numeric_measurement_inputs",
                    "partial_hold_routing_rule",
                    "transition_levels",
                ],
                "transition_levels_required_exact": [
                    "INTERNAL_CONSISTENCY_ONLY",
                    "EXTERNALLY_COMPARABLE_CANDIDATE",
                    "PROBE_READY",
                    "PREDICTIVELY_CONFIRMED",
                ],
                "enforce_non_reopen_during_formalization": True,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "formalization_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_PROBE_READINESS_STANDARD_FORMALIZATION_OUTCOME",
                "no_loop_rule": "ONE_PROBE_READINESS_STANDARD_FORMALIZATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED",
                    "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE",
                    "PROBE_READINESS_STANDARD_FORMALIZATION_CONTRACT_VIOLATION",
                    "HOLD_PENDING_POLICY_REPAIR",
                ],
                "default_outcome": "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    selection_outcome: str = "RESTART_MODE_SELECTED_POLICY_LANE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_common_failure_modes_synthesis_20260412_v0.json",
        {"summary": {"terminal_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "probe_readiness_standard_candidate_20260412_v0.json",
        {
            "summary": {"terminal_outcome": "REQUIRES_RESTART_SELECTION_LAYER"},
            "probe_readiness_standard_candidate": {
                "comparator_fidelity_minimum": "DECLARED_AND_MACHINE_CHECKABLE",
                "repeatability_stability_minimum": "DECLARED_AND_MACHINE_CHECKABLE",
                "observable_mapping_minimum": "DECLARED_AND_MACHINE_CHECKABLE",
                "numeric_measurement_inputs": "MANDATORY_BEFORE_PROBE_READY",
                "partial_hold_routing_rule": "PARTIAL_HOLD_REQUIRES_POLICY_OR_CLOSURE_NO_UNBOUNDED_RETRY_LOOP",
                "transition_levels": [
                    "INTERNAL_CONSISTENCY_ONLY",
                    "EXTERNALLY_COMPARABLE_CANDIDATE",
                    "PROBE_READY",
                    "PREDICTIVELY_CONFIRMED",
                ],
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_mode_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": selection_outcome,
                "selected_restart_mode": "NEW_POLICY_EVIDENCE_STANDARD_LANE",
            }
        },
    )


def test_reports_probe_readiness_standard_formalized_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_FORMALIZATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED"


def test_reports_probe_readiness_standard_formalization_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_FORMALIZATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selection_outcome="RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE"


def test_reports_probe_readiness_standard_formalization_contract_violation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_FORMALIZATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selection_outcome="RESTART_MODE_SELECTED_UNTOUCHED_LANE")
    selection_path = (
        tmp_path / "formal" / "output" / "reports" / "science_restart_mode_selection_20260412_v0.json"
    )
    selection = json.loads(selection_path.read_text(encoding="utf-8"))
    selection["summary"]["selected_restart_mode"] = "GENUINELY_UNTOUCHED_LANE"
    selection_path.write_text(json.dumps(selection, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE"


def test_reports_hold_pending_policy_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_FORMALIZATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)
    candidate_path = (
        tmp_path / "formal" / "output" / "reports" / "probe_readiness_standard_candidate_20260412_v0.json"
    )
    candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
    candidate["probe_readiness_standard_candidate"]["transition_levels"] = ["BROKEN"]
    candidate_path.write_text(json.dumps(candidate, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE"
