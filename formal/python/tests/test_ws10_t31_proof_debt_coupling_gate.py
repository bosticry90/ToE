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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_31_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T31_PROOF_DEBT_COUPLING_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t31_proof_debt_coupling_checkpoint_20260406_v0.json"
TRACEABILITY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0.md"
BURNDOWN_PACKET_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md"
BURNDOWN_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle05_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t31_proof_debt_coupling_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t31_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 31 declaration."
    assert DECISION_PATH.exists(), "Missing T31 proof-debt coupling decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T31 checkpoint json artifact."
    assert TRACEABILITY_PATH.exists(), "Missing proof-debt traceability doc."
    assert BURNDOWN_PACKET_PATH.exists(), "Missing proof-debt burndown packet."
    assert BURNDOWN_CHECKPOINT_PATH.exists(), "Missing proof-debt burndown checkpoint."
    assert GATE_PATH.exists(), "Missing T31 gate file."


def test_ws10_t31_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_31_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T31_PROOF_DEBT_COUPLING_DECISION_20260406_v0.md",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_CHECKPOINT_JSON_v0: formal/output/ws10_t31_proof_debt_coupling_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_GATE_v0: formal/python/tests/test_ws10_t31_proof_debt_coupling_gate.py",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_ENTRY_CRITERIA_v0: REQUIRES_T30_ACCEPTANCE_PLUS_PACKET05_OPERATIONALIZATION_PARITY",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_PROOF_DEBT_SCOPE_TOKEN_v0: CONTROL_SURFACE_PROOF_DEBT_COUPLING_NONLIVE",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_TRACEABILITY_POINTER_v0: formal/docs/release/TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0.md",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_BURNDOWN_PACKET_POINTER_v0: formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_BURNDOWN_CHECKPOINT_POINTER_v0: formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_COUPLING_RESULT_v0: ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_ORPHAN_BINDING_STATUS_v0: NO_ORPHAN_PROOF_DEBT_ROWS_v0",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_STOP_CONDITION_v0: HALT_ON_PROOF_DEBT_DRIFT_OR_ORPHAN_BINDING_OR_LIVE_TOKEN",
        "THEORY_RESTART_T31_REMEDIATION_PHASE_E_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T31_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t31_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_E_T31_STATUS_v0: ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_E_T31_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_31_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_E_T31_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T31_PROOF_DEBT_COUPLING_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_E_T31_CHECKPOINT_JSON_v0: formal/output/ws10_t31_proof_debt_coupling_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_E_T31_GATE_v0: formal/python/tests/test_ws10_t31_proof_debt_coupling_gate.py",
        "WS10_REMEDIATION_PHASE_E_T31_ENTRY_CRITERIA_v0: REQUIRES_T30_ACCEPTANCE_PLUS_PACKET05_OPERATIONALIZATION_PARITY",
        "WS10_REMEDIATION_PHASE_E_T31_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_E_T31_PROOF_DEBT_SCOPE_TOKEN_v0: CONTROL_SURFACE_PROOF_DEBT_COUPLING_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T31_TRACEABILITY_POINTER_v0: formal/docs/release/TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0.md",
        "WS10_REMEDIATION_PHASE_E_T31_BURNDOWN_PACKET_POINTER_v0: formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md",
        "WS10_REMEDIATION_PHASE_E_T31_BURNDOWN_CHECKPOINT_POINTER_v0: formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json",
        "WS10_REMEDIATION_PHASE_E_T31_COUPLING_RESULT_v0: ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_E_T31_ORPHAN_BINDING_STATUS_v0: NO_ORPHAN_PROOF_DEBT_ROWS_v0",
        "WS10_REMEDIATION_PHASE_E_T31_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_E_T31_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_E_T31_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_E_T31_STOP_CONDITION_v0: HALT_ON_PROOF_DEBT_DRIFT_OR_ORPHAN_BINDING_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_E_T31_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_E_T31_ADJUDICATION_v0: PROOF_DEBT_COUPLING_BINDINGS_PINNED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase E T31 token(s): " + ", ".join(missing)


def test_ws10_t31_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)
    traceability_text = _read(TRACEABILITY_PATH)
    burndown_payload = _json(BURNDOWN_CHECKPOINT_PATH)

    assert "coupling_result_token: ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0" in decision_text
    assert "proof_debt_scope_token: CONTROL_SURFACE_PROOF_DEBT_COUPLING_NONLIVE" in decision_text
    assert "orphan_binding_status_token: NO_ORPHAN_PROOF_DEBT_ROWS_v0" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("proof_debt_scope_token") == "CONTROL_SURFACE_PROOF_DEBT_COUPLING_NONLIVE"
    assert payload.get("coupling_result") == "ACTIVE_PROOF_DEBT_WITNESS_COUPLING_NONLIVE_v0"
    assert payload.get("orphan_binding_status") == "NO_ORPHAN_PROOF_DEBT_ROWS_v0"
    assert payload.get("orphan_binding_count") == 0

    assert "TOE_PROOF_DEBT_TRACEABILITY_STATUS_v0: ACTIVE_BOUNDED_NONCLAIM" in traceability_text
    assert "TOE_PROOF_DEBT_TRACEABILITY_GAPID_CLASS_v0: OPEN_PROOF_DEBT" in traceability_text
    assert burndown_payload.get("status_summary", {}).get("critical_pending_tokens_remaining") == 0
