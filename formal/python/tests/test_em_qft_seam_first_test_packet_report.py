from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_seam_first_test_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, structure_sufficient: bool = True, signal_observed: bool = False) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_post_qm_stat_rebalance_report": "formal/output/reports/science_post_qm_stat_rebalance_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_m4_seam_closure_promotion_cycle01": "formal/output/em_m4_seam_closure_promotion_cycle01_v0.json",
                "qft_m4_seam_closure_promotion_cycle01": "formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json"
            },
            "first_test_policy": {
                "required_rebalance_outcome": "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE",
                "required_gr_freeze_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_target_seam": "SEAM-EM-QFT",
                "required_em_m4_status": "COMPLETE_BOUNDED_v0",
                "required_qft_m4_status": "COMPLETE_BOUNDED_v0",
                "em_qft_declared_structure_sufficient": structure_sufficient,
                "em_qft_signal_observed": signal_observed,
                "single_execution_only": True,
                "single_ruling_only": True
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "EM_QFT_SEAM_SIGNAL_PRODUCED",
                    "EM_QFT_SEAM_VALID_BUT_NONMOVING",
                    "EM_QFT_SEAM_REQUIRES_UNDECLARED_STRUCTURE",
                    "EM_QFT_SEAM_PATH_FALSIFIED"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_FIRST_TEST_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_FIRST_TEST_PACKET_ONLY",
                "default_outcome": "EM_QFT_SEAM_PATH_FALSIFIED"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    rebalance_outcome: str = "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE",
    gr_freeze_outcome: str = "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
    gr_row_frozen: bool = True,
    seam_id: str = "SEAM-EM-QFT",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_qm_stat_rebalance_20260412_v0.json",
        {"summary": {"selected_outcome": rebalance_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": gr_freeze_outcome,
                "row_001_attack_class_cycling_frozen": gr_row_frozen,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "em_m4_seam_closure_promotion_cycle01_v0.json",
        {
            "payload": {
                "status": "COMPLETE_BOUNDED_v0",
                "basis": {"required_seams": [{"seam_id": seam_id}]},
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "qft_m4_seam_closure_promotion_cycle01_v0.json",
        {
            "payload": {
                "status": "COMPLETE_BOUNDED_v0",
                "basis": {"required_seams": [{"seam_id": seam_id}]},
            }
        },
    )


def test_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_SEAM_FIRST_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_SEAM_VALID_BUT_NONMOVING"


def test_reports_signal_produced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_SEAM_FIRST_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, signal_observed=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_SEAM_SIGNAL_PRODUCED"


def test_reports_requires_undeclared_structure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_SEAM_FIRST_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, structure_sufficient=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_SEAM_REQUIRES_UNDECLARED_STRUCTURE"


def test_reports_path_falsified_when_gr_not_frozen(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_SEAM_FIRST_TEST_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, gr_row_frozen=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_SEAM_PATH_FALSIFIED"
