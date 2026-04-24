from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_27_DECLARATION_20260406_v0.md"
SCOPE_LOCK_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T27_SINGLE_LANE_SCOPE_LOCK_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t27_scope_lock_checkpoint_20260406_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t27_single_lane_scope_lock_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t27_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 27 declaration."
    assert SCOPE_LOCK_PATH.exists(), "Missing T27 scope-lock artifact."
    assert CHECKPOINT_PATH.exists(), "Missing Tranche 27 checkpoint artifact."
    assert GATE_PATH.exists(), "Missing Tranche 27 gate file."


def test_ws10_t27_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE_SINGLE_LANE_SCOPE_LOCK_NONLIVE",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_27_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_SCOPE_LOCK_ARTIFACT_v0: formal/docs/release/WS_10_T27_SINGLE_LANE_SCOPE_LOCK_20260406_v0.md",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t27_scope_lock_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_GATE_v0: formal/python/tests/test_ws10_t27_single_lane_scope_lock_gate.py",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_ENTRY_CRITERIA_v0: REQUIRES_T26_ACCEPTANCE_PLUS_SINGLE_LANE_NONLIVE_AUTHORIZATION_PLUS_SCOPE_LOCK_BOUNDARY_DECLARATION",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_SCOPE_TOKEN_v0: CONTROL_SURFACE_SCOPE_LOCK_SINGLE_LANE_A1_GR_QM_NONLIVE",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_AUTHORIZED_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_STOP_CONDITION_v0: HALT_ON_SCOPE_DRIFT_OR_ANY_EXECUTION_LIVE_TOKEN",
        "THEORY_RESTART_T27_REMEDIATION_PHASE_E_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T27_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t27_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_E_T27_STATUS_v0: ACTIVE_SINGLE_LANE_SCOPE_LOCK_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T27_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_27_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_E_T27_SCOPE_LOCK_ARTIFACT_v0: formal/docs/release/WS_10_T27_SINGLE_LANE_SCOPE_LOCK_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_E_T27_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t27_scope_lock_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_E_T27_GATE_v0: formal/python/tests/test_ws10_t27_single_lane_scope_lock_gate.py",
        "WS10_REMEDIATION_PHASE_E_T27_ENTRY_CRITERIA_v0: REQUIRES_T26_ACCEPTANCE_PLUS_SINGLE_LANE_NONLIVE_AUTHORIZATION_PLUS_SCOPE_LOCK_BOUNDARY_DECLARATION",
        "WS10_REMEDIATION_PHASE_E_T27_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_E_T27_SCOPE_TOKEN_v0: CONTROL_SURFACE_SCOPE_LOCK_SINGLE_LANE_A1_GR_QM_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T27_AUTHORIZED_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_E_T27_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_E_T27_STOP_CONDITION_v0: HALT_ON_SCOPE_DRIFT_OR_ANY_EXECUTION_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_E_T27_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_E_T27_ADJUDICATION_v0: SINGLE_LANE_SCOPE_LOCK_PINNED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase E T27 token(s): " + ", ".join(missing)


def test_ws10_t27_scope_lock_checkpoint_binding() -> None:
    scope_lock_text = _read(SCOPE_LOCK_PATH)
    checkpoint = _json(CHECKPOINT_PATH)

    assert "authorized_lane_token: A1_GR_QM_SEAM_PROMOTION" in scope_lock_text
    assert "paused_lane_token: A1_BR01_DISPERSION_TO_METRIC" in scope_lock_text
    assert "execution_live_token_count: 0" in scope_lock_text
    assert "scope_token: CONTROL_SURFACE_SCOPE_LOCK_SINGLE_LANE_A1_GR_QM_NONLIVE" in scope_lock_text
    assert "stop_condition_token: HALT_ON_SCOPE_DRIFT_OR_ANY_EXECUTION_LIVE_TOKEN" in scope_lock_text
    assert "theorem_surface_target: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean" in scope_lock_text

    assert checkpoint.get("status") == "ACTIVE_SINGLE_LANE_SCOPE_LOCK_NONLIVE"
    assert checkpoint.get("anchored_commit") == "522eedb"
    assert checkpoint.get("execution_live_token_count") == 0
    assert checkpoint.get("scope_token") == "CONTROL_SURFACE_SCOPE_LOCK_SINGLE_LANE_A1_GR_QM_NONLIVE"
    assert checkpoint.get("authorized_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert checkpoint.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert checkpoint.get("stop_condition") == "HALT_ON_SCOPE_DRIFT_OR_ANY_EXECUTION_LIVE_TOKEN"
    assert checkpoint.get("locked_theorem_surface") == "formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean"


def test_ws10_t27_scope_lock_verification_ladder_tokens() -> None:
    text = _read(SCOPE_LOCK_PATH)
    required = [
        "formal/python/tests/test_ws10_t26_dual_candidate_lane_selection_gate.py",
        "formal/python/tests/test_ws10_t27_single_lane_scope_lock_gate.py",
        "formal/python/tests/test_toe_qft_gr_seam_packet42_hold_fork_decision_gate.py",
    ]
    for token in required:
        assert token in text, f"Missing verification ladder token: {token}"


def test_ws10_t27_status_vocabulary_is_closed() -> None:
    surfaces = [
        _active_text(STATE_PATH),
        _active_text(ROADMAP_PATH),
        _read(PROGRAM_PATH),
        _read(SCOPE_LOCK_PATH),
    ]

    required_values = {
        "A1_GR_QM_SEAM_PROMOTION",
        "A1_BR01_DISPERSION_TO_METRIC",
        "AUTHORIZED_SINGLE_LANE_NONLIVE",
        "PAUSED_DEFERRED_NONLIVE",
        "CONTROL_SURFACE_SCOPE_LOCK_SINGLE_LANE_A1_GR_QM_NONLIVE",
    }
    for value in required_values:
        assert any(value in text for text in surfaces), f"Missing required scope-lock value: {value}"

    forbidden_values = [
        "AUTHORIZED_SINGLE_LANE_LIVE",
        "DUAL_LANE_LIVE",
        "BR01_REACTIVATED",
    ]
    for forbidden in forbidden_values:
        assert all(forbidden not in text for text in surfaces), (
            f"Forbidden live-status vocabulary present: {forbidden}"
        )
