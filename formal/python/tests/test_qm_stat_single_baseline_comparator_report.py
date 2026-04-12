from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_single_baseline_comparator_report as comparator_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str = "placeholder\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_seam": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
                "source_signature_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "source_signature_id": "QM_STAT_CYCLE11_MASS_AND_HIGHER_MOMENT_PARITY_SIGNATURE_v0",
            },
            "baseline_comparator": {
                "baseline_count": 1,
                "baseline_id": "OV-RL-10",
                "baseline_name": "RL10_ENTROPY_BALANCE",
                "baseline_schema": "OV-RL-10_entropy_balance_comparator/v0",
                "selection_reason": "Pinned stat-facing comparator.",
                "lock_markdown": "formal/markdown/locks/observables/OV-RL-10_entropy_balance_v0.md",
                "front_door_contract": "formal/docs/rl10_entropy_balance_v0_front_door_contract.md",
                "reference_artifact": "formal/external_evidence/rl10_entropy_balance_domain_01/rl10_reference_report.json",
                "candidate_artifact": "formal/external_evidence/rl10_entropy_balance_domain_01/rl10_candidate_report.json",
            },
            "comparison_spec": {
                "compared_observable": "FINITE_SUPPORT_PROBABILITY_MASS_AND_HIGHER_CENTRAL_MOMENT_PARITY_SIGNATURE",
                "comparison_method": "MAP_QM_STAT_SIGNATURE_TO_RL10_STATIONARY_DISTRIBUTION_AND_ENTROPY_BALANCE_INTERFACE",
                "external_comparability_threshold": "REQUIRES_SINGLE_BASELINE_ALIGNMENT_AND_RL10_INTERFACE_FIELDS",
                "numerical_probe_ready_threshold": "REQUIRES_SINGLE_BASELINE_ALIGNMENT_AND_ONE_BOUNDED_NUMERICAL_PROBE",
                "non_separation_rule": "IF_INTERFACE_FIELDS_ABSENT_CLASSIFY_INTERNAL_ONLY_REMAINS",
            },
            "execution_policy": {
                "single_baseline_only": True,
                "single_baseline_only_rule": "ONE_DECLARED_BASELINE_COMPARATOR_ONLY",
                "no_loop_rule": "ONE_SINGLE_BASELINE_COMPARATOR_DECLARATION_ONLY",
            },
        },
    )


def _write_source_signature(path: Path) -> None:
    _write_json(
        path,
        {
            "blocker_discharge_criteria": {
                "shared_support": [0, 1, 2],
                "qm_probability_mass": ["1/4", "1/2", "1/4"],
                "stat_probability_mass": ["1/4", "1/2", "1/4"],
                "eighteenth_central_moment": {"qm_m18": "1/1", "stat_m18": "1/1"},
            },
            "bounded_incompatibility_exclusion": {"classification": "NONCOMPATIBLE_EXCLUDED_v0"},
        },
    )


def test_qm_stat_single_baseline_comparator_declares_complete_single_baseline(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(comparator_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_SINGLE_BASELINE_COMPARATOR_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_source_signature(tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json")
    _write_text(tmp_path / "formal" / "markdown" / "locks" / "observables" / "OV-RL-10_entropy_balance_v0.md")
    _write_text(tmp_path / "formal" / "docs" / "rl10_entropy_balance_v0_front_door_contract.md")
    _write_json(
        tmp_path / "formal" / "external_evidence" / "rl10_entropy_balance_domain_01" / "rl10_reference_report.json",
        {"schema": "RL/entropy_balance_front_door_report/v1"},
    )
    _write_json(
        tmp_path / "formal" / "external_evidence" / "rl10_entropy_balance_domain_01" / "rl10_candidate_report.json",
        {"schema": "RL/entropy_balance_front_door_report/v1"},
    )

    report = comparator_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["comparator_status"] == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
    assert report["summary"]["baseline_id"] == "OV-RL-10"
    assert report["summary"]["candidate_mapping_status"] == "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY"


def test_qm_stat_single_baseline_comparator_fails_closed_when_multiple_baselines_are_declared(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(comparator_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_SINGLE_BASELINE_COMPARATOR_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["baseline_comparator"]["baseline_count"] = 2
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    _write_source_signature(tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json")
    _write_text(tmp_path / "formal" / "markdown" / "locks" / "observables" / "OV-RL-10_entropy_balance_v0.md")
    _write_text(tmp_path / "formal" / "docs" / "rl10_entropy_balance_v0_front_door_contract.md")
    _write_json(
        tmp_path / "formal" / "external_evidence" / "rl10_entropy_balance_domain_01" / "rl10_reference_report.json",
        {"schema": "RL/entropy_balance_front_door_report/v1"},
    )
    _write_json(
        tmp_path / "formal" / "external_evidence" / "rl10_entropy_balance_domain_01" / "rl10_candidate_report.json",
        {"schema": "RL/entropy_balance_front_door_report/v1"},
    )

    report = comparator_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["comparator_status"] == "COMPARATOR_DECLARATION_INCOMPLETE"
    assert report["summary"]["next_action"] == "REPAIR_QM_STAT_SINGLE_BASELINE_COMPARATOR_DECLARATION_ONCE"
