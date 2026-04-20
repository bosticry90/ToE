from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_stat_cycle12_continuation_execution_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_surface": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "source_lane": "QM_STAT_CYCLE11",
                "authorized_candidate_target": "CYCLE12",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "domain": "seam",
            },
            "required_inputs": {
                "qm_stat_cycle11_explicit_downstream_authorization_report": "formal/output/reports/qm_stat_cycle11_explicit_downstream_authorization_20260419_v0.json",
                "cycle12_candidate_doc": "formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
                "cycle12_target_doc": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_v0.md",
                "cycle12_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                "cycle12_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
            },
            "continuation_execution_contract": {
                "required_authorization_outcome": "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0",
                "required_authorization_next_action": "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE12_CONTINUATION_ONLY",
                "required_authorization_scope_token": "CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE",
                "required_branch_chain_status": "UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
                "required_candidate_tokens": [
                    "WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM",
                    "WS10_T20_QM_STAT_CYCLE12_LANE_v0: QM_STAT",
                    "WS10_T20_QM_STAT_CYCLE12_TARGET_v0: CYCLE12",
                    "WS10_T20_QM_STAT_CYCLE12_ARTIFACT_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                    "WS10_T20_QM_STAT_CYCLE12_GATE_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
                ],
                "required_target_doc_tokens": [
                    "QM_STAT_CYCLE12_STATUS_v0: TWENTIETH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
                    "QM_STAT_CYCLE12_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_FOURTEENTH_SIXTEENTH_EIGHTEENTH_AND_TWENTIETH_MOMENT_PARITY_REQUIRED",
                    "QM_STAT_CYCLE12_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
                    "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_STATUS_v0: CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
                ],
                "required_gate_tokens": [
                    "cycle=12,",
                    "QM_STAT_CYCLE12_STATUS_v0: TWENTIETH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
                    "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_STATUS_v0: CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
                ],
                "required_artifact_status": "CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
                "required_adjudication": "NOT_YET_DISCHARGED",
                "execution_scope_token": "QM_STAT_CYCLE12_SINGLE_BOUNDED_CONTINUATION_EXECUTION_ONLY_NONLIVE",
                "execution_live_token_count": 0,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "continuation_execution_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "QM_STAT_CYCLE12_CONTINUATION_EXECUTED_NONLIVE",
                    "QM_STAT_CYCLE12_CONTINUATION_BLOCKED",
                    "QM_STAT_CYCLE12_CONTINUATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_REPAIR",
                ],
                "default_outcome": "QM_STAT_CYCLE12_CONTINUATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    authorization_outcome: str = "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_cycle11_explicit_downstream_authorization_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": authorization_outcome,
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "source_lane": "QM_STAT_CYCLE11",
                "authorized_candidate_target": "CYCLE12",
                "authorization_scope_token": "CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE",
                "branch_chain_status": "UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
                "selected_candidate_artifact_pointer": "formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
                "selected_target_artifact_pointer": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                "selected_target_gate_pointer": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
                "next_action": "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE12_CONTINUATION_ONLY",
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "\n".join(
            [
                "- `WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM`",
                "- `WS10_T20_QM_STAT_CYCLE12_LANE_v0: QM_STAT`",
                "- `WS10_T20_QM_STAT_CYCLE12_TARGET_v0: CYCLE12`",
                "- `WS10_T20_QM_STAT_CYCLE12_ARTIFACT_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json`",
                "- `WS10_T20_QM_STAT_CYCLE12_GATE_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py`",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_v0.md",
        "\n".join(
            [
                "- `QM_STAT_CYCLE12_STATUS_v0: TWENTIETH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM`",
                "- `QM_STAT_CYCLE12_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_FOURTEENTH_SIXTEENTH_EIGHTEENTH_AND_TWENTIETH_MOMENT_PARITY_REQUIRED`",
                "- `QM_STAT_CYCLE12_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM`",
                "- `QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_STATUS_v0: CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM`",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        {
            "artifact_id": "qm_stat_class_b_seam_physics_pilot_cycle12_v0",
            "status": "CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
            "adjudication": {"value": "NOT_YET_DISCHARGED"},
        },
    )
    _write_text(
        root / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "\n".join(
            [
                "register_qm_stat_cycle_gate_suite(",
                "    globals(),",
                "    QmStatCycleGateSpec(",
                "        cycle=12,",
                "        doc_status_token=\"QM_STAT_CYCLE12_STATUS_v0: TWENTIETH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM\",",
                "        cycle_status_doc_token=\"QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_STATUS_v0: CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM\",",
                "    ),",
                ")",
            ]
        ),
    )


def test_reports_cycle12_continuation_executed_nonlive(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE12_CONTINUATION_EXECUTED_NONLIVE"
    assert report["summary"]["execution_scope_token"] == "QM_STAT_CYCLE12_SINGLE_BOUNDED_CONTINUATION_EXECUTION_ONLY_NONLIVE"


def test_reports_cycle12_continuation_blocked_without_authorization(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, authorization_outcome="QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_BLOCKED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE12_CONTINUATION_BLOCKED"


def test_live_cycle12_continuation_execution_report_matches_current_repo_state() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_state_tokens = [
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_DECLARATION_v0: formal/docs/release/QM_STAT_CYCLE12_CONTINUATION_EXECUTION_20260419_v0.json",
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_REPORT_TOOL_v0: formal/python/tools/qm_stat_cycle12_continuation_execution_report.py",
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_REPORT_JSON_v0: formal/output/reports/qm_stat_cycle12_continuation_execution_20260419_v0.json",
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_GATE_v0: formal/python/tests/test_qm_stat_cycle12_continuation_execution_report.py",
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_OUTCOME_v0: QM_STAT_CYCLE12_CONTINUATION_EXECUTED_NONLIVE",
        "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_NEXT_ACTION_v0: STOP_AT_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_TOKEN_PENDING_ANY_FURTHER_DOWNSTREAM_AUTHORIZATION",
    ]
    for token in required_state_tokens:
        assert token in state_text

    required_roadmap_refs = [
        "formal/docs/release/QM_STAT_CYCLE12_CONTINUATION_EXECUTION_20260419_v0.json",
        "formal/output/reports/qm_stat_cycle12_continuation_execution_20260419_v0.json",
        "formal/python/tests/test_qm_stat_cycle12_continuation_execution_report.py",
    ]
    for ref in required_roadmap_refs:
        assert ref in roadmap_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_cycle12_continuation_execution_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE12_CONTINUATION_EXECUTED_NONLIVE"
    assert (
        report["summary"]["next_action"]
        == "STOP_AT_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_TOKEN_PENDING_ANY_FURTHER_DOWNSTREAM_AUTHORIZATION"
    )
    assert report["summary"]["selected_target_gate_pointer"] == "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py"
