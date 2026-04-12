from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import shared_model_class_comparator_binding_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    binding_confirmed: bool = False,
    probe_ready_from_binding: bool = False,
    binding_partial_evidence: bool = True,
    path_falsified: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "shared_model_class_post_signal_interpretation_report": "formal/output/reports/shared_model_class_post_signal_interpretation_20260412_v0.json",
                "shared_model_class_first_bounded_test_packet_report": "formal/output/reports/shared_model_class_first_bounded_test_packet_20260412_v0.json",
                "shared_model_class_program_proposal_report": "formal/output/reports/shared_model_class_program_proposal_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "binding_policy": {
                "required_interpretation_outcome": "SHARED_MODEL_CLASS_EXTERNALLY_COMPARABLE_CANDIDATE",
                "required_interpretation_next_action": "OPEN_ONE_BOUNDED_COMPARATOR_BINDING_STEP",
                "required_first_test_outcome": "SHARED_MODEL_CLASS_SIGNAL_PRODUCED",
                "required_proposal_outcome": "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "single_comparator": {
                    "comparator_id": "EXT-COMP-SHARED-TRANSPORT-0001",
                    "description": "desc",
                },
                "single_bound_quantity": {
                    "quantity_id": "shared_bridge_transport_interface_residual",
                    "description": "desc",
                },
                "single_comparator_only": True,
                "single_quantity_only": True,
                "binding_executable_under_declared_structure": True,
                "binding_confirmed": binding_confirmed,
                "probe_ready_from_binding": probe_ready_from_binding,
                "binding_partial_evidence": binding_partial_evidence,
                "path_falsified": path_falsified,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "binding_contract": {
                "allowed_outcomes": [
                    "SHARED_MODEL_CLASS_COMPARATOR_BINDING_CONFIRMED",
                    "SHARED_MODEL_CLASS_PROBE_READY",
                    "SHARED_MODEL_CLASS_BINDING_PARTIAL_HOLD",
                    "SHARED_MODEL_CLASS_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_COMPARATOR_BINDING_OUTCOME",
                "no_loop_rule": "ONE_SHARED_MODEL_CLASS_COMPARATOR_BINDING_STEP_ONLY",
                "default_outcome": "SHARED_MODEL_CLASS_BINDING_PARTIAL_HOLD",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    interpretation_outcome: str = "SHARED_MODEL_CLASS_EXTERNALLY_COMPARABLE_CANDIDATE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_signal_interpretation_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": interpretation_outcome,
                "next_action": "OPEN_ONE_BOUNDED_COMPARATOR_BINDING_STEP",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_first_bounded_test_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": "SHARED_MODEL_CLASS_SIGNAL_PRODUCED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_program_proposal_20260412_v0.json",
        {"summary": {"terminal_outcome": "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED"}},
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


def test_reports_binding_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    _write_declaration(declaration_path, binding_confirmed=False, binding_partial_evidence=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_BINDING_PARTIAL_HOLD"


def test_reports_binding_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    _write_declaration(declaration_path, binding_confirmed=True, probe_ready_from_binding=False, binding_partial_evidence=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_COMPARATOR_BINDING_CONFIRMED"


def test_reports_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    _write_declaration(declaration_path, binding_confirmed=True, probe_ready_from_binding=True, binding_partial_evidence=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_PROBE_READY"


def test_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    _write_declaration(declaration_path, path_falsified=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_PATH_FALSIFIED"
