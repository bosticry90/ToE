from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import shared_model_class_post_signal_interpretation_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_internal_coherence: bool = True,
    external_comparator_candidate_ready: bool = True,
    probe_readiness_ready: bool = False,
    signal_strength_sufficient: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "shared_model_class_first_bounded_test_packet_report": "formal/output/reports/shared_model_class_first_bounded_test_packet_20260412_v0.json",
                "shared_model_class_program_proposal_report": "formal/output/reports/shared_model_class_program_proposal_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "interpretation_policy": {
                "required_first_test_outcome": "SHARED_MODEL_CLASS_SIGNAL_PRODUCED",
                "required_first_test_next_action": "OPEN_POST_SIGNAL_INTERPRETATION_LAYER",
                "required_proposal_outcome": "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "signal_internal_coherence": signal_internal_coherence,
                "external_comparator_candidate_ready": external_comparator_candidate_ready,
                "probe_readiness_ready": probe_readiness_ready,
                "signal_strength_sufficient": signal_strength_sufficient,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "interpretation_contract": {
                "allowed_outcomes": [
                    "SHARED_MODEL_CLASS_INTERNAL_SIGNAL_ONLY",
                    "SHARED_MODEL_CLASS_EXTERNALLY_COMPARABLE_CANDIDATE",
                    "SHARED_MODEL_CLASS_PROBE_READY",
                    "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_OUTCOME",
                "no_loop_rule": "ONE_SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_LAYER_ONLY",
                "default_outcome": "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD",
            },
        },
    )


def _seed_inputs(root: Path, *, first_test_outcome: str = "SHARED_MODEL_CLASS_SIGNAL_PRODUCED") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_first_bounded_test_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": first_test_outcome,
                "next_action": "OPEN_POST_SIGNAL_INTERPRETATION_LAYER",
            }
        },
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


def test_reports_externally_comparable_candidate(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    _write_declaration(declaration_path, signal_internal_coherence=True, external_comparator_candidate_ready=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_EXTERNALLY_COMPARABLE_CANDIDATE"


def test_reports_internal_signal_only(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    _write_declaration(declaration_path, signal_internal_coherence=True, external_comparator_candidate_ready=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_INTERNAL_SIGNAL_ONLY"


def test_reports_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    _write_declaration(declaration_path, signal_internal_coherence=True, external_comparator_candidate_ready=True, probe_readiness_ready=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_PROBE_READY"


def test_reports_signal_insufficient_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    _write_declaration(declaration_path, signal_strength_sufficient=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD"
