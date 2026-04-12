from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import proof_debt_active_cluster_next_tranche_focus_report as focus_tool
from formal.python.tools import proof_debt_active_cluster_surface_ruling_report as ruling_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_surface_ruling_deprioritizes_executed_non_moving_surface(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(ruling_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_MATH_PD_C05_BURNDOWN_GATE_20260411_v0.json"
    )
    tranche_report_path = (
        tmp_path
        / "formal"
        / "output"
        / "reports"
        / "proof_debt_active_cluster_surface_tranche_report_20260411_v0.json"
    )

    _write_json(
        declaration_path,
        {
            "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
            "target_surface": {
                "surface_id": "MATH-PD-C05-BURNDOWN-GATE",
                "surface_path": "formal/python/tests/test_proof_debt_burndown_cycle05_gate.py",
            },
            "required_inputs": {
                "surface_tranche_report": "formal/output/reports/proof_debt_active_cluster_surface_tranche_report_20260411_v0.json"
            },
        },
    )
    _write_json(
        tranche_report_path,
        {
            "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
            "summary": {
                "tranche_outcome": "SURFACE_EXECUTED_NO_BLOCKER_MOVEMENT",
                "target_surface_id": "MATH-PD-C05-BURNDOWN-GATE",
                "target_surface_path": "formal/python/tests/test_proof_debt_burndown_cycle05_gate.py",
                "surface_gate_passed": True,
                "movement_signals": {
                    "theorem_gap_state_changed": False,
                    "seam_integration_state_changed": False,
                    "global_row_success_state_changed": False,
                    "blocker_state_token_changed": False,
                },
            },
        },
    )

    report = ruling_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["surface_ruling"] == "SURFACE_EXECUTED_VALID_NO_BLOCKER_MOVEMENT"
    assert report["summary"]["gate_passed"] is True
    assert report["summary"]["blocker_facing_movement_observed"] is False
    assert report["summary"]["exclude_from_immediate_reselection"] is True
    assert report["summary"]["deprioritized_as_immediate_blocker_facing_next_tranche_surface"] is True


def test_focus_report_skips_surface_with_non_moving_ruling(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(focus_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROOF_DEBT_ACTIVE_CLUSTER_NEXT_TRANCHE_FOCUS_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
            "required_inputs": {
                "packet_report": "formal/output/reports/proof_debt_first_formal_campaign_packet_report_20260411_v0.json",
                "discharge_tranche_report": "formal/output/reports/proof_debt_first_formal_campaign_discharge_tranche_report_20260411_v0.json",
                "trend_pointer": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_pointer": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_pointer": "formal/output/reports/physics_progress_ledger_v0.json",
                "surface_ruling_reports": [
                    "formal/output/reports/proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json"
                ],
            },
            "selection_policy": {
                "required_direct_impact_signals": [
                    "plausible_theorem_gap_delta_lt_0_path",
                    "plausible_seam_integration_gap_delta_lt_0_path",
                    "plausible_global_row_success_increment_path",
                    "explicit_blocker_state_token_transition_path",
                ],
                "weights": {
                    "plausible_theorem_gap_delta_lt_0_path": 5,
                    "plausible_seam_integration_gap_delta_lt_0_path": 3,
                    "plausible_global_row_success_increment_path": 4,
                    "explicit_blocker_state_token_transition_path": 6,
                    "terminal_gate_coupling": 5,
                    "traceability_only_surface": -3,
                },
            },
            "surface_candidates": [
                {
                    "surface_id": "MATH-PD-C05-BURNDOWN-GATE",
                    "surface_path": "formal/python/tests/test_proof_debt_burndown_cycle05_gate.py",
                    "surface_kind": "gate_test",
                    "priority_note": "Original highest-score surface.",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": True,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": True,
                        "explicit_blocker_state_token_transition_path": True,
                        "terminal_gate_coupling": True,
                        "traceability_only_surface": False,
                    },
                },
                {
                    "surface_id": "MATH-PD-C05-MARKER-STABILITY-GATE",
                    "surface_path": "formal/python/tests/test_proof_debt_marker_stability_gate.py",
                    "surface_kind": "gate_test",
                    "priority_note": "Should become the next eligible surface.",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": True,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": False,
                        "explicit_blocker_state_token_transition_path": True,
                        "terminal_gate_coupling": False,
                        "traceability_only_surface": False,
                    },
                },
            ],
        },
    )

    _write_json(
        reports_dir / "proof_debt_first_formal_campaign_packet_report_20260411_v0.json",
        {"summary": {"selected_cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01"}},
    )
    _write_json(
        reports_dir / "proof_debt_first_formal_campaign_discharge_tranche_report_20260411_v0.json",
        {
            "summary": {
                "tranche_state": "PROOF_DEBT_DISCHARGE_PARTIAL_FORMAL_PROGRESS_NO_BLOCKER_MOVE",
                "theorem_gap_delta": 0,
                "seam_integration_gap_delta": 0,
                "global_row_success_count": 0,
            }
        },
    )
    _write_json(reports_dir / "governance_blocker_trend_window_20260410_v0.json", {"blocker_counts": {"net_delta": 0}})
    _write_json(
        reports_dir / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {}}}},
    )
    _write_json(reports_dir / "physics_progress_ledger_v0.json", {"progress_classification": "REWORK_ROUTED"})
    _write_json(
        reports_dir / "proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json",
        {
            "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
            "summary": {
                "surface_id": "MATH-PD-C05-BURNDOWN-GATE",
                "surface_ruling": "SURFACE_EXECUTED_VALID_NO_BLOCKER_MOVEMENT",
                "allocation_decision": "DEPRIORITIZE_AS_IMMEDIATE_BLOCKER_FACING_NEXT_TRANCHE_SURFACE",
                "exclude_from_immediate_reselection": True,
            },
        },
    )

    tests_dir = tmp_path / "formal" / "python" / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)
    (tests_dir / "test_proof_debt_burndown_cycle05_gate.py").write_text("", encoding="utf-8")
    (tests_dir / "test_proof_debt_marker_stability_gate.py").write_text("", encoding="utf-8")

    report = focus_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["selected_surface_id"] == "MATH-PD-C05-MARKER-STABILITY-GATE"
    assert report["summary"]["excluded_surface_ids"] == ["MATH-PD-C05-BURNDOWN-GATE"]
    ranked_surfaces = report["objective_quality"]["inputs"]["ranked_surfaces"]
    assert ranked_surfaces[0]["surface_id"] == "MATH-PD-C05-MARKER-STABILITY-GATE"
    assert ranked_surfaces[1]["surface_id"] == "MATH-PD-C05-BURNDOWN-GATE"
    assert ranked_surfaces[1]["excluded_from_immediate_reselection"] is True
