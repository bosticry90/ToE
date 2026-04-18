from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_33_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T33_QM_STAT_CYCLE12_CONTINUATION_AUTHORIZATION_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t33_qm_stat_cycle12_continuation_checkpoint_20260406_v0.json"
T32_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t32_authority_convergence_checkpoint_20260406_v0.json"
CANDIDATE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md"
TARGET_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle12_v0.json"
TARGET_GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t33_qm_stat_cycle12_continuation_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t33_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 33 declaration."
    assert DECISION_PATH.exists(), "Missing T33 continuation authorization decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T33 checkpoint json artifact."
    assert T32_CHECKPOINT_PATH.exists(), "Missing T32 predecessor checkpoint json artifact."
    assert CANDIDATE_DOC_PATH.exists(), "Missing QM_STAT cycle12 candidate declaration doc."
    assert TARGET_ARTIFACT_PATH.exists(), "Missing QM_STAT cycle12 target artifact."
    assert TARGET_GATE_PATH.exists(), "Missing QM_STAT cycle12 target gate."
    assert GATE_PATH.exists(), "Missing T33 gate file."


def test_ws10_t33_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_STATUS_v0: ACTIVE_QM_STAT_CYCLE12_BOUNDED_CONTINUATION_AUTHORIZED_NONLIVE_v0",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_33_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T33_QM_STAT_CYCLE12_CONTINUATION_AUTHORIZATION_DECISION_20260406_v0.md",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_CHECKPOINT_JSON_v0: formal/output/ws10_t33_qm_stat_cycle12_continuation_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_GATE_v0: formal/python/tests/test_ws10_t33_qm_stat_cycle12_continuation_gate.py",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_ENTRY_CRITERIA_v0: REQUIRES_T32_ACCEPTANCE_PLUS_EXPLICIT_SINGLE_LANE_CONTINUATION_AUTHORIZATION",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_CONTINUATION_SCOPE_TOKEN_v0: CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_CANDIDATE_ARTIFACT_POINTER_v0: formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_TARGET_ARTIFACT_POINTER_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_TARGET_GATE_POINTER_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_CONTINUATION_RESULT_v0: QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_STOP_CONDITION_v0: HALT_ON_CONTINUATION_SCOPE_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "THEORY_RESTART_T33_CONTINUATION_PHASE_G_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T33_CONTINUATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t33_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_G_T33_STATUS_v0: ACTIVE_QM_STAT_CYCLE12_BOUNDED_CONTINUATION_AUTHORIZED_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_G_T33_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_33_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_G_T33_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T33_QM_STAT_CYCLE12_CONTINUATION_AUTHORIZATION_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_G_T33_CHECKPOINT_JSON_v0: formal/output/ws10_t33_qm_stat_cycle12_continuation_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_G_T33_GATE_v0: formal/python/tests/test_ws10_t33_qm_stat_cycle12_continuation_gate.py",
        "WS10_REMEDIATION_PHASE_G_T33_ENTRY_CRITERIA_v0: REQUIRES_T32_ACCEPTANCE_PLUS_EXPLICIT_SINGLE_LANE_CONTINUATION_AUTHORIZATION",
        "WS10_REMEDIATION_PHASE_G_T33_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_G_T33_CONTINUATION_SCOPE_TOKEN_v0: CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE",
        "WS10_REMEDIATION_PHASE_G_T33_CANDIDATE_ARTIFACT_POINTER_v0: formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "WS10_REMEDIATION_PHASE_G_T33_TARGET_ARTIFACT_POINTER_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        "WS10_REMEDIATION_PHASE_G_T33_TARGET_GATE_POINTER_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
        "WS10_REMEDIATION_PHASE_G_T33_CONTINUATION_RESULT_v0: QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_G_T33_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_G_T33_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_G_T33_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_G_T33_STOP_CONDITION_v0: HALT_ON_CONTINUATION_SCOPE_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_G_T33_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_G_T33_ADJUDICATION_v0: QM_STAT_CYCLE12_CONTINUATION_AUTHORIZATION_PINNED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase G T33 token(s): " + ", ".join(missing)


def test_ws10_t33_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)
    predecessor = _json(T32_CHECKPOINT_PATH)
    candidate_text = _read(CANDIDATE_DOC_PATH)

    assert "continuation_result_token: QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0" in decision_text
    assert "continuation_scope_token: CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE" in decision_text
    assert "selected_candidate_lane_token: QM_STAT" in decision_text
    assert "selected_candidate_target_token: CYCLE12" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_QM_STAT_CYCLE12_BOUNDED_CONTINUATION_AUTHORIZED_NONLIVE_v0"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("continuation_scope_token") == "CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE"
    assert payload.get("continuation_result") == "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0"
    assert payload.get("selected_candidate_lane") == "QM_STAT"
    assert payload.get("selected_candidate_target") == "CYCLE12"

    assert "WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM" in candidate_text
    assert predecessor.get("status") == "ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0"
