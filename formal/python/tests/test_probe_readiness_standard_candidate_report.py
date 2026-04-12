from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import probe_readiness_standard_candidate_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    requires_restart_selection_layer: bool = True,
    architecture_review_required: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_common_failure_modes_synthesis_report": "formal/output/reports/science_common_failure_modes_synthesis_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "governance_blocker_trend_window_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
            },
            "candidate_policy": {
                "required_synthesis_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
                "required_qm_stat_policy_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "required_trend_movement_status": "FLAT",
                "required_trend_net_delta": 0,
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
                "requires_restart_selection_layer": requires_restart_selection_layer,
                "architecture_review_required": architecture_review_required,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "candidate_contract": {
                "required_standard_keys": [
                    "comparator_fidelity_minimum",
                    "repeatability_stability_minimum",
                    "observable_mapping_minimum",
                    "numeric_measurement_inputs",
                    "partial_hold_routing_rule",
                    "transition_levels",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_PROBE_READINESS_STANDARD_CANDIDATE_OUTCOME",
                "no_loop_rule": "ONE_PROBE_READINESS_STANDARD_CANDIDATE_LAYER_ONLY",
                "allowed_outcomes": [
                    "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED",
                    "PROBE_READINESS_STANDARD_EVIDENCE_INCOMPLETE",
                    "REQUIRES_RESTART_SELECTION_LAYER",
                    "HOLD_PENDING_ARCHITECTURE_REVIEW",
                ],
                "default_outcome": "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED",
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
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json",
        {
            "trend_summary": {"movement_status": "FLAT"},
            "blocker_counts": {"net_delta": 0},
        },
    )


def test_reports_requires_restart_selection_layer(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_CANDIDATE_20260412_v0.json"
    )
    _write_declaration(declaration_path, requires_restart_selection_layer=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_RESTART_SELECTION_LAYER"


def test_reports_probe_readiness_standard_candidate_drafted(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_CANDIDATE_20260412_v0.json"
    )
    _write_declaration(declaration_path, requires_restart_selection_layer=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED"


def test_reports_probe_readiness_standard_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_CANDIDATE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, synthesis_outcome="COMMON_FAILURE_MODES_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PROBE_READINESS_STANDARD_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_architecture_review(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROBE_READINESS_STANDARD_CANDIDATE_20260412_v0.json"
    )
    _write_declaration(declaration_path, architecture_review_required=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_ARCHITECTURE_REVIEW"
