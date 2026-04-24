from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_36_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T36_QM_STAT_FORWARD_BOUNDED_EXECUTION_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t36_qm_stat_forward_bounded_execution_checkpoint_20260406_v0.json"
T35_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t35_qm_stat_forward_continuation_selection_checkpoint_20260406_v0.json"
CANDIDATE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md"
TARGET_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle12_v0.json"
TARGET_GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t36_qm_stat_forward_bounded_execution_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t36_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 36 declaration."
    assert DECISION_PATH.exists(), "Missing T36 forward bounded execution decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T36 checkpoint json artifact."
    assert T35_CHECKPOINT_PATH.exists(), "Missing T35 predecessor checkpoint json artifact."
    assert CANDIDATE_DOC_PATH.exists(), "Missing QM_STAT cycle12 candidate declaration doc."
    assert TARGET_ARTIFACT_PATH.exists(), "Missing QM_STAT cycle12 target artifact."
    assert TARGET_GATE_PATH.exists(), "Missing QM_STAT cycle12 target gate."
    assert GATE_PATH.exists(), "Missing T36 gate file."


def test_ws10_t36_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_STATUS_v0: ACTIVE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE_v0",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_36_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T36_QM_STAT_FORWARD_BOUNDED_EXECUTION_DECISION_20260406_v0.md",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_CHECKPOINT_JSON_v0: formal/output/ws10_t36_qm_stat_forward_bounded_execution_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_GATE_v0: formal/python/tests/test_ws10_t36_qm_stat_forward_bounded_execution_gate.py",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_ENTRY_CRITERIA_v0: REQUIRES_T35_ACCEPTANCE_PLUS_QM_STAT_FORWARD_CONTINUATION_SELECTION",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_FORWARD_EXECUTION_SCOPE_TOKEN_v0: CONTROL_SURFACE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_SELECTED_BRANCH_TOKEN_v0: QM_STAT_FORWARD_CONTINUATION",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_CANDIDATE_ARTIFACT_POINTER_v0: formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_TARGET_ARTIFACT_POINTER_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_TARGET_GATE_POINTER_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_FORWARD_EXECUTION_RESULT_v0: QM_STAT_FORWARD_BOUNDED_EXECUTION_PINNED_NONLIVE_v0",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_STOP_CONDITION_v0: HALT_ON_FORWARD_EXECUTION_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "THEORY_RESTART_T36_EXECUTION_PHASE_J_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T36_EXECUTION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t36_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_J_T36_STATUS_v0: ACTIVE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_J_T36_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_36_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_J_T36_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T36_QM_STAT_FORWARD_BOUNDED_EXECUTION_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_J_T36_CHECKPOINT_JSON_v0: formal/output/ws10_t36_qm_stat_forward_bounded_execution_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_J_T36_GATE_v0: formal/python/tests/test_ws10_t36_qm_stat_forward_bounded_execution_gate.py",
        "WS10_REMEDIATION_PHASE_J_T36_ENTRY_CRITERIA_v0: REQUIRES_T35_ACCEPTANCE_PLUS_QM_STAT_FORWARD_CONTINUATION_SELECTION",
        "WS10_REMEDIATION_PHASE_J_T36_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_J_T36_FORWARD_EXECUTION_SCOPE_TOKEN_v0: CONTROL_SURFACE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE",
        "WS10_REMEDIATION_PHASE_J_T36_SELECTED_BRANCH_TOKEN_v0: QM_STAT_FORWARD_CONTINUATION",
        "WS10_REMEDIATION_PHASE_J_T36_CANDIDATE_ARTIFACT_POINTER_v0: formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "WS10_REMEDIATION_PHASE_J_T36_TARGET_ARTIFACT_POINTER_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        "WS10_REMEDIATION_PHASE_J_T36_TARGET_GATE_POINTER_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "WS10_REMEDIATION_PHASE_J_T36_FORWARD_EXECUTION_RESULT_v0: QM_STAT_FORWARD_BOUNDED_EXECUTION_PINNED_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_J_T36_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_J_T36_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_J_T36_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_J_T36_STOP_CONDITION_v0: HALT_ON_FORWARD_EXECUTION_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_J_T36_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_J_T36_ADJUDICATION_v0: QM_STAT_FORWARD_BOUNDED_EXECUTION_PINNED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase J T36 token(s): " + ", ".join(missing)


def test_ws10_t36_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)
    predecessor = _json(T35_CHECKPOINT_PATH)
    candidate_text = _read(CANDIDATE_DOC_PATH)

    assert "forward_execution_result_token: QM_STAT_FORWARD_BOUNDED_EXECUTION_PINNED_NONLIVE_v0" in decision_text
    assert "forward_execution_scope_token: CONTROL_SURFACE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE" in decision_text
    assert "selected_branch_token: QM_STAT_FORWARD_CONTINUATION" in decision_text
    assert "selected_lane_token: QM_STAT" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE_v0"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("forward_execution_scope_token") == "CONTROL_SURFACE_QM_STAT_FORWARD_BOUNDED_EXECUTION_NONLIVE"
    assert payload.get("forward_execution_result") == "QM_STAT_FORWARD_BOUNDED_EXECUTION_PINNED_NONLIVE_v0"
    assert payload.get("selected_branch") == "QM_STAT_FORWARD_CONTINUATION"
    assert payload.get("selected_lane") == "QM_STAT"

    assert "WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM" in candidate_text
    assert predecessor.get("status") == "ACTIVE_QM_STAT_FORWARD_CONTINUATION_SELECTION_NONLIVE_v0"
