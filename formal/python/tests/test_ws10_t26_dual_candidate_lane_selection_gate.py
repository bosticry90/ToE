from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_26_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T26_DUAL_CANDIDATE_LANE_SELECTION_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t26_single_lane_authorization_checkpoint_20260406_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t26_dual_candidate_lane_selection_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t26_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 26 declaration."
    assert DECISION_PATH.exists(), "Missing Tranche 26 decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing Tranche 26 checkpoint artifact."
    assert GATE_PATH.exists(), "Missing Tranche 26 gate file."


def test_ws10_t26_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE_SINGLE_LANE_DECISION_AUTHORIZATION_NONCLAIM",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_26_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T26_DUAL_CANDIDATE_LANE_SELECTION_DECISION_20260406_v0.md",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t26_single_lane_authorization_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_GATE_v0: formal/python/tests/test_ws10_t26_dual_candidate_lane_selection_gate.py",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_ENTRY_CRITERIA_v0: REQUIRES_T25_ACCEPTANCE_PLUS_TWO_PINNED_CANDIDATES_PLUS_DECISION_ONLY_SCOPE",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_CANDIDATE_COUNT_v0: 2",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_AUTHORIZATION_STATE_v0: ONE_LANE_AUTHORIZED_ONE_LANE_PAUSED_NONLIVE",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_AUTHORIZED_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_AUTHORIZED_LANE_STATUS_v0: AUTHORIZED_SINGLE_LANE_NONLIVE",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_PAUSED_LANE_STATUS_v0: PAUSED_DEFERRED_NONLIVE",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_NO_THIRD_STATUS_VALUES_v0: ENFORCED",
        "THEORY_RESTART_T26_REMEDIATION_PHASE_E_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T26_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t26_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_E_T26_STATUS_v0: ACTIVE_SINGLE_LANE_DECISION_AUTHORIZATION_NONCLAIM",
        "WS10_REMEDIATION_PHASE_E_T26_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_26_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_E_T26_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T26_DUAL_CANDIDATE_LANE_SELECTION_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_E_T26_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t26_single_lane_authorization_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_E_T26_GATE_v0: formal/python/tests/test_ws10_t26_dual_candidate_lane_selection_gate.py",
        "WS10_REMEDIATION_PHASE_E_T26_ENTRY_CRITERIA_v0: REQUIRES_T25_ACCEPTANCE_PLUS_TWO_PINNED_CANDIDATES_PLUS_DECISION_ONLY_SCOPE",
        "WS10_REMEDIATION_PHASE_E_T26_CANDIDATE_COUNT_v0: 2",
        "WS10_REMEDIATION_PHASE_E_T26_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_E_T26_AUTHORIZATION_STATE_v0: ONE_LANE_AUTHORIZED_ONE_LANE_PAUSED_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T26_AUTHORIZED_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_E_T26_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_E_T26_AUTHORIZED_LANE_STATUS_v0: AUTHORIZED_SINGLE_LANE_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T26_PAUSED_LANE_STATUS_v0: PAUSED_DEFERRED_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T26_NO_THIRD_STATUS_VALUES_v0: ENFORCED",
        "WS10_REMEDIATION_PHASE_E_T26_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_E_T26_ADJUDICATION_v0: DECISION_RECORDED_ONE_AUTHORIZED_ONE_PAUSED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase E T26 token(s): " + ", ".join(missing)


def test_ws10_t26_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    checkpoint = _json(CHECKPOINT_PATH)

    assert "declared_winner_lane: A1_GR_QM_SEAM_PROMOTION" in decision_text
    assert "declared_loser_lane: A1_BR01_DISPERSION_TO_METRIC" in decision_text
    assert "authorized_lane_status: AUTHORIZED_SINGLE_LANE_NONLIVE" in decision_text
    assert "paused_lane_status: PAUSED_DEFERRED_NONLIVE" in decision_text
    assert "no_third_status_values: ENFORCED" in decision_text

    assert checkpoint.get("declared_winner_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert checkpoint.get("declared_loser_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert checkpoint.get("authorized_lane_status") == "AUTHORIZED_SINGLE_LANE_NONLIVE"
    assert checkpoint.get("paused_lane_status") == "PAUSED_DEFERRED_NONLIVE"
    assert checkpoint.get("no_third_status_values") == "ENFORCED"
    assert checkpoint.get("execution_live_token_count") == 0
    assert checkpoint.get("candidate_count") == 2
    assert checkpoint.get("anchored_commit") == "522eedb"


def test_ws10_t26_status_vocabulary_is_closed() -> None:
    surfaces = [
        _active_text(STATE_PATH),
        _active_text(ROADMAP_PATH),
        _read(PROGRAM_PATH),
        _read(DECISION_PATH),
    ]

    required_values = {
        "A1_GR_QM_SEAM_PROMOTION",
        "A1_BR01_DISPERSION_TO_METRIC",
        "AUTHORIZED_SINGLE_LANE_NONLIVE",
        "PAUSED_DEFERRED_NONLIVE",
    }
    for value in required_values:
        assert any(value in text for text in surfaces), f"Missing required decision value: {value}"

    forbidden_values = [
        "PREFERRED",
        "REVIEWABLE",
        "CONDITIONAL_AUTHORIZED",
        "SOFT_AUTHORIZED",
        "SOFT_PAUSED",
    ]
    for forbidden in forbidden_values:
        assert all(forbidden not in text for text in surfaces), (
            f"Forbidden third-status vocabulary present: {forbidden}"
        )
