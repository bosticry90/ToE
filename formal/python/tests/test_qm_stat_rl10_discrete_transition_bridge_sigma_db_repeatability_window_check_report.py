from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_sigma_db_repeatability_window_check_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    window_half_width: float = 0.02,
    stability_floor: float = 0.02,
    sample_perturbations: list[float] | None = None,
    not_a_full_second_cycle: bool = True,
    no_scope_expansion: bool = True,
) -> None:
    if sample_perturbations is None:
        sample_perturbations = [0.0, 0.01, 0.02]
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_probe_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
                "bridge_material_repeatability_admissibility_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "named_check_id": "rl10_bridge_sigma_db_repeatability_window_check_v0",
                "check_family_id": "REPEATABILITY_STABILITY_WINDOW_FAMILY",
            },
            "window_parameters": {
                "window_half_width": window_half_width,
                "stability_floor": stability_floor,
                "n_sample_points": len(sample_perturbations),
                "sample_perturbations": sample_perturbations,
            },
            "check_policy": {
                "required_naming_review_outcome": "BOUNDED_REPEATABILITY_CHECK_NAMED",
                "required_naming_check_id": "rl10_bridge_sigma_db_repeatability_window_check_v0",
                "required_admissibility_criteria_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
                "not_a_full_second_cycle": not_a_full_second_cycle,
                "no_scope_expansion": no_scope_expansion,
                "single_declared_surface_only": True,
            },
            "check_contract": {
                "allowed_outcomes": [
                    "WINDOW_CHECK_COMPARATOR_STABLE",
                    "WINDOW_CHECK_COMPARATOR_NOT_STABLE",
                    "WINDOW_CHECK_SCOPE_VIOLATION",
                    "WINDOW_CHECK_PRECONDITION_FAILED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_WINDOW_CHECK_OUTCOME",
                "no_loop_rule": "ONE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_ONLY",
                "default_outcome": "WINDOW_CHECK_COMPARATOR_NOT_STABLE",
                "stop_after": "WINDOW_CHECK_RULING_FOCUSED_GATES_REFRESHED_TOKEN_READ",
            },
        },
    )


def _seed_probe_execution(
    root: Path,
    *,
    signal_margin: float = 0.04,
    probe_signal_strength: float = 0.11,
    probe_signal_threshold: float = 0.07,
    terminal_outcome: str = "PROBE_SIGNAL_CONFIRMED",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "signal_margin": signal_margin,
                    "probe_signal_strength": probe_signal_strength,
                    "probe_signal_threshold": probe_signal_threshold,
                }
            },
            "summary": {
                "terminal_outcome": terminal_outcome,
                "signal_margin": signal_margin,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
        },
    )


def _seed_naming_review(
    root: Path,
    *,
    review_outcome: str = "BOUNDED_REPEATABILITY_CHECK_NAMED",
    proposed_check_name: str = "rl10_bridge_sigma_db_repeatability_window_check_v0",
    proposed_check_kind: str = "REPEATABILITY",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "proposed_check_name": proposed_check_name,
                "proposed_check_kind": proposed_check_kind,
            }
        },
    )


def _seed_admissibility(
    root: Path,
    *,
    terminal_outcome: str = "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": terminal_outcome,
            }
        },
    )


def test_window_check_comparator_stable_at_boundary(tmp_path: Path, monkeypatch) -> None:
    """Canonical case: min margin (0.04 - 0.02 = 0.02) is at the stability floor — passes."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_20260422_v0.json"
    )
    _write_declaration(
        declaration_path,
        window_half_width=0.02,
        stability_floor=0.02,
        sample_perturbations=[0.0, 0.01, 0.02],
    )
    _seed_probe_execution(tmp_path, signal_margin=0.04)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["window_check_outcome"] == "WINDOW_CHECK_COMPARATOR_STABLE"
    assert report["summary"]["window_check_comparator_stable"] is True
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    assert report["objective_quality"]["criteria"]["preconditions_satisfied"] is True
    assert report["objective_quality"]["criteria"]["window_check_executed"] is True
    assert report["objective_quality"]["criteria"]["all_criteria_satisfied"] is True
    sampled = report["objective_quality"]["window_execution"]["sampled_margins"]
    assert len(sampled) == 3
    assert min(sampled) == pytest.approx(0.02, abs=1e-9)


def test_window_check_comparator_not_stable_when_margin_too_small(
    tmp_path: Path, monkeypatch
) -> None:
    """Signal margin too small: min margin drops well below stability floor."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_20260422_v0.json"
    )
    _write_declaration(
        declaration_path,
        window_half_width=0.03,
        stability_floor=0.02,
        sample_perturbations=[0.0, 0.015, 0.03],
    )
    # signal_margin=0.04, max_perturbation=0.03 → min_margin=0.01 < stability_floor=0.02
    _seed_probe_execution(tmp_path, signal_margin=0.04)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["window_check_outcome"] == "WINDOW_CHECK_COMPARATOR_NOT_STABLE"
    assert report["summary"]["window_check_comparator_stable"] is False
    assert report["objective_quality"]["criteria"]["window_check_executed"] is True
    assert report["objective_quality"]["window_execution"]["window_check_passes"] is False


def test_window_check_scope_violation_when_naming_outcome_wrong(
    tmp_path: Path, monkeypatch
) -> None:
    """Naming outcome wrong but comparator/quantity/check_id scope still correct → SCOPE_VIOLATION."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_probe_execution(tmp_path)
    _seed_naming_review(tmp_path, review_outcome="WRONG_OUTCOME")
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["window_check_outcome"] == "WINDOW_CHECK_SCOPE_VIOLATION"
    assert report["summary"]["window_check_comparator_stable"] is False
    assert report["criteria"]["naming_review_outcome_is_bounded_check_named"] is False


def test_window_check_precondition_failed_when_comparator_id_wrong(
    tmp_path: Path, monkeypatch
) -> None:
    """Wrong probe comparator_id makes scope itself inadmissible → PRECONDITION_FAILED."""
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_probe_execution(tmp_path, comparator_id="WRONG-COMPARATOR")
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["window_check_outcome"] == "WINDOW_CHECK_PRECONDITION_FAILED"
    assert report["summary"]["window_check_comparator_stable"] is False
    assert report["criteria"]["comparator_id_matches_scope"] is False


def test_window_check_enforces_no_promotion_no_closure_always(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_probe_execution(tmp_path)
    _seed_naming_review(tmp_path)
    _seed_admissibility(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
    next_action = report["summary"]["next_action"]
    assert "PROMOTION" not in next_action
    assert "CLOSURE" not in next_action
    assert report["summary"]["check_id"] == "rl10_bridge_sigma_db_repeatability_window_check_v0"
    assert report["summary"]["window_half_width"] == pytest.approx(0.02, abs=1e-9)
    assert report["summary"]["stability_floor"] == pytest.approx(0.02, abs=1e-9)
