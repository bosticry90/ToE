from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_post_first_test_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    packet_shape_refinement_viable: bool = False,
    different_subseam_indicated: bool = False,
    require_rescoring: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "em_qft_seam_first_test_packet_report": "formal/output/reports/em_qft_seam_first_test_packet_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "science_post_qm_stat_rebalance_report": "formal/output/reports/science_post_qm_stat_rebalance_20260412_v0.json"
            },
            "decision_policy": {
                "required_first_test_outcome": "EM_QFT_SEAM_VALID_BUT_NONMOVING",
                "required_target_seam": "SEAM-EM-QFT",
                "require_gr_row_001_frozen": True,
                "require_qm_stat_untouched_hold": True,
                "packet_shape_refinement_viable": packet_shape_refinement_viable,
                "different_subseam_indicated": different_subseam_indicated,
                "require_rescoring": require_rescoring,
                "single_decision_only": True,
                "single_outcome_only": True
            },
            "decision_contract": {
                "allowed_outcomes": [
                    "ACTIVATE_EM_QFT_SIGNAL_REFINEMENT_PACKET",
                    "ACTIVATE_EM_QFT_DIFFERENT_TARGET_SUBSEAM",
                    "HOLD_EM_QFT_AND_REQUIRE_RESCORING",
                    "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_POST_FIRST_TEST_DECISION_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_POST_FIRST_TEST_DECISION_ONLY",
                "default_outcome": "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    first_test_outcome: str = "EM_QFT_SEAM_VALID_BUT_NONMOVING",
    gr_row_frozen: bool = True,
    qm_hold: str = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_seam_first_test_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": first_test_outcome,
                "target_seam": "SEAM-EM-QFT",
            },
            "objective_quality": {
                "inputs": {
                    "em_qft_declared_structure_sufficient": True
                }
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {
            "summary": {
                "row_001_attack_class_cycling_frozen": gr_row_frozen,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_qm_stat_rebalance_20260412_v0.json",
        {
            "summary": {
                "qm_stat_bridge_state": qm_hold,
            }
        },
    )


def test_reports_requires_different_attack_class_by_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_POST_FIRST_TEST_DECISION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS"


def test_reports_signal_refinement_packet(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_POST_FIRST_TEST_DECISION_20260412_v0.json"
    _write_declaration(declaration_path, packet_shape_refinement_viable=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_EM_QFT_SIGNAL_REFINEMENT_PACKET"


def test_reports_different_subseam(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_POST_FIRST_TEST_DECISION_20260412_v0.json"
    _write_declaration(declaration_path, different_subseam_indicated=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_EM_QFT_DIFFERENT_TARGET_SUBSEAM"


def test_reports_hold_and_rescore_when_preconditions_break(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_POST_FIRST_TEST_DECISION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, gr_row_frozen=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
