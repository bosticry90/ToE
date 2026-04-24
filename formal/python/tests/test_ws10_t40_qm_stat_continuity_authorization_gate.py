from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_40_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T40_QM_STAT_CONTINUITY_AUTHORIZATION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t40_qm_stat_continuity_authorization_checkpoint_20260406_v0.json"
T39_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t39_qm_stat_boundary_decision_checkpoint_20260406_v0.json"
CANDIDATE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md"
TARGET_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle12_v0.json"
TARGET_GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t40_qm_stat_continuity_authorization_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t40_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 40 declaration."
    assert DECISION_PATH.exists(), "Missing T40 continuity authorization decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T40 checkpoint json artifact."
    assert T39_CHECKPOINT_PATH.exists(), "Missing T39 predecessor checkpoint json artifact."
    assert CANDIDATE_DOC_PATH.exists(), "Missing QM_STAT cycle12 candidate declaration doc."
    assert TARGET_ARTIFACT_PATH.exists(), "Missing QM_STAT cycle12 target artifact."
    assert TARGET_GATE_PATH.exists(), "Missing QM_STAT cycle12 target gate."
    assert GATE_PATH.exists(), "Missing T40 gate file."


def test_ws10_t40_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_STATUS_v0: ACTIVE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE_v0",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_40_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T40_QM_STAT_CONTINUITY_AUTHORIZATION_20260406_v0.md",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_CHECKPOINT_JSON_v0: formal/output/ws10_t40_qm_stat_continuity_authorization_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_GATE_v0: formal/python/tests/test_ws10_t40_qm_stat_continuity_authorization_gate.py",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_ENTRY_CRITERIA_v0: REQUIRES_T39_ACCEPTANCE_PLUS_QM_STAT_CONTINUITY_AUTHORIZATION",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_CONTINUITY_AUTHORIZATION_SCOPE_TOKEN_v0: CONTROL_SURFACE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_SELECTED_BRANCH_TOKEN_v0: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_PATH",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_CANDIDATE_ARTIFACT_POINTER_v0: formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_TARGET_ARTIFACT_POINTER_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_TARGET_GATE_POINTER_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_CONTINUITY_AUTHORIZATION_RESULT_v0: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_NONLIVE_v0",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_PHASE_M_OPERATIONALIZATION_v0: PHASE_M_BOUNDARY_DECISION_OPERATIONALIZED_BY_PHASE_N_CONTINUITY_AUTHORIZATION_v0",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_STOP_CONDITION_v0: HALT_ON_CONTINUITY_AUTHORIZATION_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "THEORY_RESTART_T40_EXECUTION_PHASE_N_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T40_EXECUTION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t40_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_N_T40_STATUS_v0: ACTIVE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_N_T40_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_40_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_N_T40_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T40_QM_STAT_CONTINUITY_AUTHORIZATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_N_T40_CHECKPOINT_JSON_v0: formal/output/ws10_t40_qm_stat_continuity_authorization_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_N_T40_GATE_v0: formal/python/tests/test_ws10_t40_qm_stat_continuity_authorization_gate.py",
        "WS10_REMEDIATION_PHASE_N_T40_ENTRY_CRITERIA_v0: REQUIRES_T39_ACCEPTANCE_PLUS_QM_STAT_CONTINUITY_AUTHORIZATION",
        "WS10_REMEDIATION_PHASE_N_T40_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_N_T40_CONTINUITY_AUTHORIZATION_SCOPE_TOKEN_v0: CONTROL_SURFACE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE",
        "WS10_REMEDIATION_PHASE_N_T40_SELECTED_BRANCH_TOKEN_v0: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_PATH",
        "WS10_REMEDIATION_PHASE_N_T40_CANDIDATE_ARTIFACT_POINTER_v0: formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "WS10_REMEDIATION_PHASE_N_T40_TARGET_ARTIFACT_POINTER_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        "WS10_REMEDIATION_PHASE_N_T40_TARGET_GATE_POINTER_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "WS10_REMEDIATION_PHASE_N_T40_CONTINUITY_AUTHORIZATION_RESULT_v0: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_N_T40_PHASE_M_OPERATIONALIZATION_v0: PHASE_M_BOUNDARY_DECISION_OPERATIONALIZED_BY_PHASE_N_CONTINUITY_AUTHORIZATION_v0",
        "WS10_REMEDIATION_PHASE_N_T40_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_N_T40_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_N_T40_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_N_T40_STOP_CONDITION_v0: HALT_ON_CONTINUITY_AUTHORIZATION_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_N_T40_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_N_T40_ADJUDICATION_v0: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase N T40 token(s): " + ", ".join(missing)


def test_ws10_t40_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)
    predecessor = _json(T39_CHECKPOINT_PATH)
    candidate_text = _read(CANDIDATE_DOC_PATH)

    assert "continuity_authorization_result_token: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_NONLIVE_v0" in decision_text
    assert "continuity_authorization_scope_token: CONTROL_SURFACE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE" in decision_text
    assert "selected_branch_token: QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_PATH" in decision_text
    assert "selected_lane_token: QM_STAT" in decision_text
    assert "phase_m_operationalization_token: PHASE_M_BOUNDARY_DECISION_OPERATIONALIZED_BY_PHASE_N_CONTINUITY_AUTHORIZATION_v0" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE_v0"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("continuity_authorization_scope_token") == "CONTROL_SURFACE_QM_STAT_PHASE_N_CONTINUITY_AUTHORIZATION_NONLIVE"
    assert payload.get("continuity_authorization_result") == "QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_NONLIVE_v0"
    assert payload.get("selected_branch") == "QM_STAT_FORWARD_CONTINUATION_EXECUTION_V2_AUTHORIZED_PATH"
    assert payload.get("selected_lane") == "QM_STAT"
    assert payload.get("phase_m_operationalization") == "PHASE_M_BOUNDARY_DECISION_OPERATIONALIZED_BY_PHASE_N_CONTINUITY_AUTHORIZATION_v0"

    assert "WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM" in candidate_text
    assert predecessor.get("status") == "ACTIVE_QM_STAT_PHASE_M_BOUNDARY_DECISION_NONLIVE_v0"
