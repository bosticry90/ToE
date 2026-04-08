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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_29_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T29_POST_T28_CONTINUITY_RECONCILIATION_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t29_post_t28_continuity_reconciliation_checkpoint_20260406_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t29_post_t28_continuity_reconciliation_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t29_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 29 declaration."
    assert DECISION_PATH.exists(), "Missing T29 continuity decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T29 checkpoint json artifact."
    assert GATE_PATH.exists(), "Missing T29 gate file."


def test_ws10_t29_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_STATUS_v0: ACTIVE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_29_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T29_POST_T28_CONTINUITY_RECONCILIATION_DECISION_20260406_v0.md",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_CHECKPOINT_JSON_v0: formal/output/ws10_t29_post_t28_continuity_reconciliation_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_GATE_v0: formal/python/tests/test_ws10_t29_post_t28_continuity_reconciliation_gate.py",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_ENTRY_CRITERIA_v0: REQUIRES_T28_ACCEPTANCE_PLUS_SINGLE_LANE_NONLIVE_CHECKPOINT_STATE",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_CONTINUITY_SCOPE_TOKEN_v0: CONTROL_SURFACE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_CONTINUITY_RESULT_v0: CLOSED_CONTINUITY_RECONCILED_SINGLE_LANE_NONLIVE_v0",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_STOP_CONDITION_v0: HALT_ON_STATUS_AMBIGUITY_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "THEORY_RESTART_T29_REMEDIATION_PHASE_C_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T29_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t29_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_C_T29_STATUS_v0: ACTIVE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE",
        "WS10_REMEDIATION_PHASE_C_T29_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_29_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_C_T29_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T29_POST_T28_CONTINUITY_RECONCILIATION_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_C_T29_CHECKPOINT_JSON_v0: formal/output/ws10_t29_post_t28_continuity_reconciliation_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_C_T29_GATE_v0: formal/python/tests/test_ws10_t29_post_t28_continuity_reconciliation_gate.py",
        "WS10_REMEDIATION_PHASE_C_T29_ENTRY_CRITERIA_v0: REQUIRES_T28_ACCEPTANCE_PLUS_SINGLE_LANE_NONLIVE_CHECKPOINT_STATE",
        "WS10_REMEDIATION_PHASE_C_T29_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_C_T29_CONTINUITY_SCOPE_TOKEN_v0: CONTROL_SURFACE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE",
        "WS10_REMEDIATION_PHASE_C_T29_CONTINUITY_RESULT_v0: CLOSED_CONTINUITY_RECONCILED_SINGLE_LANE_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_C_T29_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_C_T29_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_C_T29_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_C_T29_STOP_CONDITION_v0: HALT_ON_STATUS_AMBIGUITY_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_C_T29_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_C_T29_ADJUDICATION_v0: POST_T28_CONTINUITY_RECONCILED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase C T29 token(s): " + ", ".join(missing)


def test_ws10_t29_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)

    assert "continuity_result_token: CLOSED_CONTINUITY_RECONCILED_SINGLE_LANE_NONLIVE_v0" in decision_text
    assert "branch_chain_status: UNAMBIGUOUS_SINGLE_ACTIVE_LANE" in decision_text
    assert "continuity_scope_token: CONTROL_SURFACE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("continuity_scope_token") == "CONTROL_SURFACE_CONTINUITY_RECONCILIATION_POST_T28_NONLIVE"
    assert payload.get("continuity_result") == "CLOSED_CONTINUITY_RECONCILED_SINGLE_LANE_NONLIVE_v0"
    assert payload.get("branch_chain_status") == "UNAMBIGUOUS_SINGLE_ACTIVE_LANE"
