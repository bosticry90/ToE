from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import shared_model_class_first_bounded_test_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    movement_signal_detected: bool = True,
    valid_but_nonmoving: bool = False,
    requires_undeclared_structure: bool = False,
    path_falsified: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "shared_model_class_program_proposal_report": "formal/output/reports/shared_model_class_program_proposal_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "test_policy": {
                "required_proposal_outcome": "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED",
                "required_proposal_next_action": "OPEN_SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_LAYER",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_frozen_lanes": ["ROW-PILLAR-GR-001", "EM-QFT"],
                "tested_shared_structure": "bridge_semantics_layer",
                "bound_minimum_components": [
                    "invariant_layer",
                    "bridge_semantics_layer",
                    "admissibility_and_comparator_binding_layer",
                ],
                "bounded_success_signal": "MATERIALIZED_SINGLE_PACKET_OUTCOME_WITH_DECLARED_COMPARATOR_BINDING",
                "shared_structure_declared": True,
                "touches_required_frozen_lanes": True,
                "comparator_binding_materialized": True,
                "movement_signal_detected": movement_signal_detected,
                "valid_but_nonmoving": valid_but_nonmoving,
                "requires_undeclared_structure": requires_undeclared_structure,
                "path_falsified": path_falsified,
                "single_packet_only": True,
                "single_outcome_only": True,
            },
            "packet_contract": {
                "allowed_outcomes": [
                    "SHARED_MODEL_CLASS_SIGNAL_PRODUCED",
                    "SHARED_MODEL_CLASS_VALID_BUT_NONMOVING",
                    "SHARED_MODEL_CLASS_REQUIRES_UNDECLARED_STRUCTURE",
                    "SHARED_MODEL_CLASS_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_FIRST_TEST_OUTCOME",
                "no_loop_rule": "ONE_SHARED_MODEL_CLASS_FIRST_TEST_PACKET_ONLY",
                "default_outcome": "SHARED_MODEL_CLASS_REQUIRES_UNDECLARED_STRUCTURE",
            },
        },
    )


def _seed_inputs(root: Path, *, proposal_outcome: str = "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_program_proposal_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": proposal_outcome,
                "next_action": "OPEN_SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_LAYER",
            },
            "proposal_payload": {
                "minimum_model_class_components": [
                    "invariant_layer",
                    "bridge_semantics_layer",
                    "admissibility_and_comparator_binding_layer",
                ]
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "row_001_attack_class_cycling_frozen": True,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_higher_level_structure_review_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_attack_class_cycling_frozen": True,
            }
        },
    )


def test_reports_signal_produced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_SIGNAL_PRODUCED"


def test_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, movement_signal_detected=False, valid_but_nonmoving=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_VALID_BUT_NONMOVING"


def test_reports_requires_undeclared_structure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, movement_signal_detected=False, requires_undeclared_structure=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_REQUIRES_UNDECLARED_STRUCTURE"


def test_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, movement_signal_detected=False, path_falsified=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_PATH_FALSIFIED"
