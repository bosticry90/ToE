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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_30_DECLARATION_20260406_v0.md"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T30_PACKET05_OPERATIONALIZATION_DECISION_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t30_packet05_operationalization_checkpoint_20260406_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "empirical_packet05_decision_ledger_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t30_packet05_operationalization_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t30_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 30 declaration."
    assert DECISION_PATH.exists(), "Missing T30 packet05 operationalization decision artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T30 checkpoint json artifact."
    assert LEDGER_PATH.exists(), "Missing packet05 decision ledger artifact."
    assert GATE_PATH.exists(), "Missing T30 gate file."


def test_ws10_t30_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_STATUS_v0: ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_30_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T30_PACKET05_OPERATIONALIZATION_DECISION_20260406_v0.md",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_CHECKPOINT_JSON_v0: formal/output/ws10_t30_packet05_operationalization_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_GATE_v0: formal/python/tests/test_ws10_t30_packet05_operationalization_gate.py",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_ENTRY_CRITERIA_v0: REQUIRES_T29_ACCEPTANCE_PLUS_SINGLE_LANE_NONLIVE_CONTINUITY_RECONCILIATION",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_PACKET05_SCOPE_TOKEN_v0: CONTROL_SURFACE_PACKET05_OPERATIONALIZATION_NONLIVE",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_PACKET05_LEDGER_POINTER_v0: formal/output/empirical_packet05_decision_ledger_v0.json",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_PACKET05_PROTOCOL_POINTER_v0: formal/docs/release/FOUNDATIONAL_EMPIRICAL_DECISION_AND_FALSIFICATION_STANDARD_v0.md",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_OPERATIONALIZATION_RESULT_v0: ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_STOP_CONDITION_v0: HALT_ON_PACKET05_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "THEORY_RESTART_T30_REMEDIATION_PHASE_D_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T30_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t30_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_D_T30_STATUS_v0: ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_D_T30_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_30_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_D_T30_DECISION_ARTIFACT_v0: formal/docs/release/WS_10_T30_PACKET05_OPERATIONALIZATION_DECISION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_D_T30_CHECKPOINT_JSON_v0: formal/output/ws10_t30_packet05_operationalization_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_D_T30_GATE_v0: formal/python/tests/test_ws10_t30_packet05_operationalization_gate.py",
        "WS10_REMEDIATION_PHASE_D_T30_ENTRY_CRITERIA_v0: REQUIRES_T29_ACCEPTANCE_PLUS_SINGLE_LANE_NONLIVE_CONTINUITY_RECONCILIATION",
        "WS10_REMEDIATION_PHASE_D_T30_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_D_T30_PACKET05_SCOPE_TOKEN_v0: CONTROL_SURFACE_PACKET05_OPERATIONALIZATION_NONLIVE",
        "WS10_REMEDIATION_PHASE_D_T30_PACKET05_LEDGER_POINTER_v0: formal/output/empirical_packet05_decision_ledger_v0.json",
        "WS10_REMEDIATION_PHASE_D_T30_PACKET05_PROTOCOL_POINTER_v0: formal/docs/release/FOUNDATIONAL_EMPIRICAL_DECISION_AND_FALSIFICATION_STANDARD_v0.md",
        "WS10_REMEDIATION_PHASE_D_T30_OPERATIONALIZATION_RESULT_v0: ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_D_T30_BRANCH_CHAIN_STATUS_v0: UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
        "WS10_REMEDIATION_PHASE_D_T30_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_D_T30_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_D_T30_STOP_CONDITION_v0: HALT_ON_PACKET05_DRIFT_OR_DUAL_LANE_OR_LIVE_TOKEN",
        "WS10_REMEDIATION_PHASE_D_T30_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_D_T30_ADJUDICATION_v0: PACKET05_OPERATIONALIZATION_BINDINGS_PINNED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase D T30 token(s): " + ", ".join(missing)


def test_ws10_t30_decision_checkpoint_binding() -> None:
    decision_text = _read(DECISION_PATH)
    payload = _json(CHECKPOINT_PATH)
    ledger = _json(LEDGER_PATH)

    assert "operationalization_result_token: ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0" in decision_text
    assert "packet05_scope_token: CONTROL_SURFACE_PACKET05_OPERATIONALIZATION_NONLIVE" in decision_text
    assert "execution_live_token_count: 0" in decision_text

    assert payload.get("status") == "ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("packet05_scope_token") == "CONTROL_SURFACE_PACKET05_OPERATIONALIZATION_NONLIVE"
    assert payload.get("operationalization_result") == "ACTIVE_PACKET05_DECISION_LEDGER_AND_FALSIFICATION_BINDINGS_NONLIVE_v0"
    assert payload.get("branch_chain_status") == "UNAMBIGUOUS_SINGLE_ACTIVE_LANE"

    assert ledger.get("ledger_id") == "empirical_packet05_decision_ledger_v0"
    rows = ledger.get("rows", {})
    assert set(rows) == {"GR", "SR"}
    for lane, row in rows.items():
        assert row.get("decision") in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}, f"Unexpected decision for {lane}"
        assert row.get("decision_record_pointer"), f"Missing decision_record_pointer for {lane}"
        assert row.get("falsification_surface_pointer"), f"Missing falsification_surface_pointer for {lane}"
