from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_row_001_new_structure_concept_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    concept_policy = {
        "target_row": "ROW-PILLAR-GR-001",
        "required_structural_gap_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
        "required_packet05_decision": "RETAIN_v0",
        "required_packet05_status": "RUN_BOUNDED_v0_NONCLAIM",
        "required_note_tokens": [
            "GR_ROW_001_NEW_STRUCTURE_STATUS_v0: CONCEPT_PACKET_LOCKED_NONEXECUTING",
            "GR_ROW_001_NEW_STRUCTURE_TARGET_ROW_v0: ROW-PILLAR-GR-001",
            "GR_ROW_001_NEW_STRUCTURE_FAMILY_v0: CROSS_REGIME_TRANSPORT_INTERFACE_MODEL_CLASS",
            "GR_ROW_001_NEW_STRUCTURE_SUCCESS_CRITERION_v0: NEW_STRUCTURE_MUST_ENABLE_BLOCKER_DELTA_OR_ROW_SUCCESS_INCREMENT",
            "GR_ROW_001_NEW_STRUCTURE_FAILURE_CRITERION_v0: IF_NO_SHARED_INTERFACE_OBSERVABLE_EXISTS_ROUTE_TO_PATH_FALSIFICATION_OR_REWORK",
            "GR_ROW_001_NEW_STRUCTURE_EXECUTION_POLICY_v0: NONEXECUTING_DESIGN_ONLY_UNTIL_P75_AND_P77_CLEAR",
        ],
        "concept_family": "CROSS_REGIME_TRANSPORT_INTERFACE_MODEL_CLASS",
        "concept_axes": [
            "shared_state_carrier",
            "cross_regime_transport_interface_map",
            "single_interface_observable",
            "fail_closed_falsification_hook",
        ],
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        concept_policy.pop("required_note_tokens")

    _write_json(
        path,
        {
            "required_inputs": {
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "toe_global_completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "gr_empirical_comparison_packet_05_artifact": "formal/output/gr_empirical_comparison_packet_05_v0.json",
                "concept_note": "formal/docs/paper/GR_ROW_001_NEW_STRUCTURE_CONCEPT_NOTE_v0.md",
            },
            "concept_policy": concept_policy,
            "concept_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_ROW_001_NEW_STRUCTURE_CONCEPT_OUTCOME",
                "no_loop_rule": "ONE_GR_ROW_001_NEW_STRUCTURE_CONCEPT_LAYER_ONLY",
                "allowed_outcomes": [
                    "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED",
                    "GR_ROW_001_NEW_STRUCTURE_CONCEPT_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_GR_ROW_001_CONCEPT_REPAIR",
                ],
                "default_outcome": "GR_ROW_001_NEW_STRUCTURE_CONCEPT_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, structural_gap_outcome: str = "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {"summary": {"terminal_outcome": structural_gap_outcome, "next_action": "FREEZE_ROW_001_ATTACK_CLASS_CYCLING_AND_DEFINE_NEW_GR_SEAM_OR_MODEL_CLASS"}},
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "ROW-PILLAR-GR-001 | pillar | GR_DERIVATION_CHAIN | SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md | formal/output/gr_empirical_comparison_packet_05_v0.json | formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py\n",
    )
    _write_json(
        root / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json",
        {"payload": {"status": "RUN_BOUNDED_v0_NONCLAIM", "decision": "RETAIN_v0"}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "GR_ROW_001_NEW_STRUCTURE_CONCEPT_NOTE_v0.md",
        "GR_ROW_001_NEW_STRUCTURE_STATUS_v0: CONCEPT_PACKET_LOCKED_NONEXECUTING\n"
        "GR_ROW_001_NEW_STRUCTURE_TARGET_ROW_v0: ROW-PILLAR-GR-001\n"
        "GR_ROW_001_NEW_STRUCTURE_FAMILY_v0: CROSS_REGIME_TRANSPORT_INTERFACE_MODEL_CLASS\n"
        "GR_ROW_001_NEW_STRUCTURE_SUCCESS_CRITERION_v0: NEW_STRUCTURE_MUST_ENABLE_BLOCKER_DELTA_OR_ROW_SUCCESS_INCREMENT\n"
        "GR_ROW_001_NEW_STRUCTURE_FAILURE_CRITERION_v0: IF_NO_SHARED_INTERFACE_OBSERVABLE_EXISTS_ROUTE_TO_PATH_FALSIFICATION_OR_REWORK\n"
        "GR_ROW_001_NEW_STRUCTURE_EXECUTION_POLICY_v0: NONEXECUTING_DESIGN_ONLY_UNTIL_P75_AND_P77_CLEAR\n",
    )


def test_reports_gr_row_001_new_structure_concept_packet_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_20260413_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED"


def test_reports_gr_row_001_new_structure_concept_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_20260413_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, structural_gap_outcome="HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_ROW_001_NEW_STRUCTURE_CONCEPT_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_gr_row_001_concept_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_20260413_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_GR_ROW_001_CONCEPT_REPAIR"