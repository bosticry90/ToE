from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import proof_debt_next_cluster_selection_report as selection_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_next_cluster_selection_skips_cluster_with_exhausted_active_surfaces(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(selection_tool, "REPO_ROOT", tmp_path)

    declaration_path = tmp_path / "formal" / "docs" / "release" / "PROOF_DEBT_NEXT_CLUSTER_SELECTION_20260411_v0.json"
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "branch_ruling_report": "formal/output/reports/proof_debt_cluster_branch_ruling_report_20260411_v0.json",
                "active_cluster_focus_report": "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_report_20260411_v0.json",
                "trend_pointer": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "ledger_pointer": "formal/output/reports/physics_progress_ledger_v0.json",
            },
            "selection_policy": {
                "exclude_from_blocker_facing_priority": ["PDC-TRACEABILITY-EMU1-01"],
                "retain_as_support_lane": ["PDC-TRACEABILITY-EMU1-01"],
                "required_direct_impact_signals": [
                    "plausible_theorem_gap_delta_lt_0_path",
                    "plausible_seam_integration_gap_delta_lt_0_path",
                    "plausible_global_row_success_increment_path",
                    "explicit_blocker_state_token_transition_path",
                ],
                "weights": {
                    "plausible_theorem_gap_delta_lt_0_path": 4,
                    "plausible_seam_integration_gap_delta_lt_0_path": 4,
                    "plausible_global_row_success_increment_path": 3,
                    "explicit_blocker_state_token_transition_path": 5,
                },
            },
            "candidate_clusters": [
                {
                    "cluster_id": "PDC-TRACEABILITY-EMU1-01",
                    "cluster_name": "traceability",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": False,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": False,
                        "explicit_blocker_state_token_transition_path": False,
                    },
                },
                {
                    "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
                    "cluster_name": "math proof debt",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": True,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": True,
                        "explicit_blocker_state_token_transition_path": True,
                    },
                },
                {
                    "cluster_id": "PDC-EMU1-DISTRIBUTIONAL-AUTH-01",
                    "cluster_name": "em u1",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": True,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": False,
                        "explicit_blocker_state_token_transition_path": True,
                    },
                },
            ],
        },
    )

    _write_json(
        reports_dir / "proof_debt_cluster_branch_ruling_report_20260411_v0.json",
        {"summary": {"branch_ruling": "CLUSTER_FULLY_DISCHARGED_NO_BLOCKER_MOVE", "allocation_decision": "REPRIORITIZE"}},
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_report_20260411_v0.json",
        {
            "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
            "summary": {
                "selection_outcome": "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE",
                "excluded_surface_ids": [
                    "MATH-PD-C05-BURNDOWN-GATE",
                    "MATH-PD-C05-MARKER-STABILITY-GATE",
                ],
            },
        },
    )
    _write_json(reports_dir / "governance_blocker_trend_window_20260410_v0.json", {"blocker_counts": {"net_delta": 0}})
    _write_json(reports_dir / "physics_progress_ledger_v0.json", {"progress_classification": "REWORK_ROUTED"})

    report = selection_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["selected_next_cluster_id"] == "PDC-EMU1-DISTRIBUTIONAL-AUTH-01"
    assert report["summary"]["exhausted_from_active_surface_selector"] == ["PDC-MATH-PROOF-DEBT-BURNDOWN-01"]
    ranked_candidates = report["objective_quality"]["inputs"]["ranked_candidates"]
    exhausted_row = next(row for row in ranked_candidates if row["cluster_id"] == "PDC-MATH-PROOF-DEBT-BURNDOWN-01")
    assert exhausted_row["exhausted_by_active_surface_selector"] is True
    assert exhausted_row["excluded_from_blocker_facing_priority"] is True


def test_next_cluster_selection_retains_prior_exhausted_cluster_via_cluster_focus_reports(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(selection_tool, "REPO_ROOT", tmp_path)

    declaration_path = tmp_path / "formal" / "docs" / "release" / "PROOF_DEBT_NEXT_CLUSTER_SELECTION_20260411_v0.json"
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "branch_ruling_report": "formal/output/reports/proof_debt_cluster_branch_ruling_report_20260411_v0.json",
                "active_cluster_focus_report": "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_report_20260411_v0.json",
                "cluster_focus_reports": [
                    "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_math_pd_burndown_20260411_v0.json",
                    "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_emu1_distributional_auth_20260411_v0.json",
                ],
                "trend_pointer": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "ledger_pointer": "formal/output/reports/physics_progress_ledger_v0.json",
            },
            "selection_policy": {
                "exclude_from_blocker_facing_priority": ["PDC-TRACEABILITY-EMU1-01"],
                "retain_as_support_lane": ["PDC-TRACEABILITY-EMU1-01"],
                "required_direct_impact_signals": [
                    "plausible_theorem_gap_delta_lt_0_path",
                    "plausible_seam_integration_gap_delta_lt_0_path",
                    "plausible_global_row_success_increment_path",
                    "explicit_blocker_state_token_transition_path",
                ],
                "weights": {
                    "plausible_theorem_gap_delta_lt_0_path": 4,
                    "plausible_seam_integration_gap_delta_lt_0_path": 4,
                    "plausible_global_row_success_increment_path": 3,
                    "explicit_blocker_state_token_transition_path": 5,
                },
            },
            "candidate_clusters": [
                {
                    "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
                    "cluster_name": "math proof debt",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": True,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": True,
                        "explicit_blocker_state_token_transition_path": True,
                    },
                },
                {
                    "cluster_id": "PDC-EMU1-DISTRIBUTIONAL-AUTH-01",
                    "cluster_name": "em u1",
                    "direct_impact_signals": {
                        "plausible_theorem_gap_delta_lt_0_path": True,
                        "plausible_seam_integration_gap_delta_lt_0_path": False,
                        "plausible_global_row_success_increment_path": False,
                        "explicit_blocker_state_token_transition_path": True,
                    },
                },
            ],
        },
    )

    _write_json(
        reports_dir / "proof_debt_cluster_branch_ruling_report_20260411_v0.json",
        {"summary": {"branch_ruling": "CLUSTER_FULLY_DISCHARGED_NO_BLOCKER_MOVE", "allocation_decision": "REPRIORITIZE"}},
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_report_20260411_v0.json",
        {
            "cluster_id": "PDC-EMU1-DISTRIBUTIONAL-AUTH-01",
            "summary": {"selection_outcome": "NEXT_ACTIVE_CLUSTER_SURFACE_SELECTED_BY_BLOCKER_LEVERAGE"},
        },
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_math_pd_burndown_20260411_v0.json",
        {
            "cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
            "summary": {"selection_outcome": "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE"},
        },
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_emu1_distributional_auth_20260411_v0.json",
        {
            "cluster_id": "PDC-EMU1-DISTRIBUTIONAL-AUTH-01",
            "summary": {"selection_outcome": "NEXT_ACTIVE_CLUSTER_SURFACE_SELECTED_BY_BLOCKER_LEVERAGE"},
        },
    )
    _write_json(reports_dir / "governance_blocker_trend_window_20260410_v0.json", {"blocker_counts": {"net_delta": 0}})
    _write_json(reports_dir / "physics_progress_ledger_v0.json", {"progress_classification": "REWORK_ROUTED"})

    report = selection_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["selected_next_cluster_id"] == "PDC-EMU1-DISTRIBUTIONAL-AUTH-01"
    assert report["summary"]["exhausted_from_active_surface_selector"] == ["PDC-MATH-PROOF-DEBT-BURNDOWN-01"]
