from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_32_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T32_AUTHORITY_CONVERGENCE_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t32_authority_convergence_checkpoint_20260406_v0.json"
T31_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t31_proof_debt_coupling_checkpoint_20260406_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t32_authority_convergence_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t32_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 32 declaration."
    assert DECISION_PATH.exists(), "Missing T32 authority convergence decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T32 checkpoint json artifact."
    assert T31_CHECKPOINT_PATH.exists(), "Missing T31 predecessor checkpoint json artifact."
    assert GATE_PATH.exists(), "Missing T32 gate file."


def test_ws10_t32_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_STATUS_v0: ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_32_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T32_AUTHORITY_CONVERGENCE_DECISION_20260406_v0.md",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_CHECKPOINT_JSON_v0: formal/output/ws10_t32_authority_convergence_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_GATE_v0: formal/python/tests/test_ws10_t32_authority_convergence_gate.py",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_ENTRY_CRITERIA_v0: REQUIRES_T31_ACCEPTANCE_PLUS_PROOF_DEBT_COUPLING_PARITY",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_CONVERGENCE_SCOPE_TOKEN_v0: CONTROL_SURFACE_AUTHORITY_CONVERGENCE_NONLIVE",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_STATE_POINTER_v0: State_of_the_Theory.md",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_ROADMAP_POINTER_v0: formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_PROGRAM_POINTER_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_CONVERGENCE_RESULT_v0: ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_STOP_CONDITION_v0: HALT_ON_CONVERGENCE_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "THEORY_RESTART_T32_REMEDIATION_PHASE_F_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T32_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t32_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_F_T32_STATUS_v0: ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_F_T32_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_32_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_F_T32_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T32_AUTHORITY_CONVERGENCE_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_F_T32_CHECKPOINT_JSON_v0: formal/output/ws10_t32_authority_convergence_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_F_T32_GATE_v0: formal/python/tests/test_ws10_t32_authority_convergence_gate.py",
        "WS10_REMEDIATION_PHASE_F_T32_ENTRY_CRITERIA_v0: REQUIRES_T31_ACCEPTANCE_PLUS_PROOF_DEBT_COUPLING_PARITY",
        "WS10_REMEDIATION_PHASE_F_T32_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_F_T32_CONVERGENCE_SCOPE_TOKEN_v0: CONTROL_SURFACE_AUTHORITY_CONVERGENCE_NONLIVE",
        "WS10_REMEDIATION_PHASE_F_T32_STATE_POINTER_v0: State_of_the_Theory.md",
        "WS10_REMEDIATION_PHASE_F_T32_ROADMAP_POINTER_v0: formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "WS10_REMEDIATION_PHASE_F_T32_PROGRAM_POINTER_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "WS10_REMEDIATION_PHASE_F_T32_CONVERGENCE_RESULT_v0: ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_F_T32_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_F_T32_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_F_T32_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_F_T32_STOP_CONDITION_v0: HALT_ON_CONVERGENCE_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_F_T32_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_F_T32_ADJUDICATION_v0: AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase F T32 token(s): " + ", ".join(missing)


def test_ws10_t32_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)
    predecessor = _json(T31_CHECKPOINT_PATH)

    assert "convergence_result_token: ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0" in decision_text
    assert "convergence_scope_token: CONTROL_SURFACE_AUTHORITY_CONVERGENCE_NONLIVE" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("convergence_scope_token") == "CONTROL_SURFACE_AUTHORITY_CONVERGENCE_NONLIVE"
    assert payload.get("convergence_result") == "ACTIVE_AUTHORITY_CONVERGENCE_ACCEPTANCE_READY_NONLIVE_v0"
    assert payload.get("branch_chain_status") == "UNAMBIGUOUS_SINGLE_ACTIVE_LANE"
    assert predecessor.get("status") == "ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0"
