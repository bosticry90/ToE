from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    admissibility_standard_defined: bool = False,
    declaration_standard_defined: bool = False,
    bounded_check_families_defined: bool = False,
    require_external_validation_policy_surface: bool = False,
    external_validation_policy_surface_defined: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json"
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "admissibility_policy": {
                "admissibility_standard_defined": admissibility_standard_defined,
                "declaration_standard_defined": declaration_standard_defined,
                "bounded_check_families_defined": bounded_check_families_defined,
                "require_external_validation_policy_surface": require_external_validation_policy_surface,
                "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
            },
            "review_contract": {
                "allowed_outcomes": [
                    "ADMISSIBILITY_STANDARD_READY_FOR_BOUNDED_CHECK_NAMING",
                    "DECLARATION_STANDARD_REQUIRED_BEFORE_NAMING",
                    "EXTERNAL_VALIDATION_POLICY_SURFACE_REQUIRED",
                    "LIMITED_HOLD_RETAINED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_ADMISSIBILITY_STANDARD_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_ONLY",
                "default_outcome": "LIMITED_HOLD_RETAINED",
            },
        },
    )


def _seed_naming_review(
    root: Path,
    *,
    naming_outcome: str = "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
    observed_comparator_id: str = "OV-RL-10",
    observed_quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": naming_outcome,
            },
            "objective_quality": {
                "inputs": {
                    "observed_comparator_id": observed_comparator_id,
                    "observed_quantity_id": observed_quantity_id,
                }
            },
        },
    )


def test_admissibility_review_reports_limited_hold_retained(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_naming_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "LIMITED_HOLD_RETAINED"


def test_admissibility_review_reports_declaration_standard_required(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_naming_review(tmp_path, naming_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "DECLARATION_STANDARD_REQUIRED_BEFORE_NAMING"


def test_admissibility_review_reports_external_validation_policy_surface_required(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        require_external_validation_policy_surface=True,
        external_validation_policy_surface_defined=False,
    )
    _seed_naming_review(tmp_path, naming_outcome="BOUNDED_CROSS_PROBE_CHECK_NAMED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "EXTERNAL_VALIDATION_POLICY_SURFACE_REQUIRED"


def test_admissibility_review_reports_ready_for_bounded_check_naming(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ADMISSIBILITY_STANDARD_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        admissibility_standard_defined=True,
        declaration_standard_defined=True,
        bounded_check_families_defined=True,
    )
    _seed_naming_review(tmp_path, naming_outcome="BOUNDED_CROSS_PROBE_CHECK_NAMED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "ADMISSIBILITY_STANDARD_READY_FOR_BOUNDED_CHECK_NAMING"
