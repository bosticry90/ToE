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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_22_DECLARATION_20260405_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "ws10_lean_proof_debt_ledger_checkpoint_20260405_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t22_phase_c_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 22 declaration."
    assert ARTIFACT_PATH.exists(), "Missing Tranche 22 checkpoint artifact."


def test_ws10_t22_phase_c_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T22_REMEDIATION_PHASE_C_STATUS_v0: ACTIVE_LEAN_PROOF_DEBT_LEDGER_KICKOFF",
        "THEORY_RESTART_T22_REMEDIATION_PHASE_C_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_22_DECLARATION_20260405_v0.md",
        "THEORY_RESTART_T22_REMEDIATION_PHASE_C_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T22_REMEDIATION_PHASE_C_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_lean_proof_debt_ledger_checkpoint_20260405_v0.json",
        "THEORY_RESTART_T22_REMEDIATION_PHASE_C_GATE_v0: formal/python/tests/test_ws10_t22_lean_proof_debt_ledger_gate.py",
        "THEORY_RESTART_T22_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]

    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t22_program_phase_c_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_C_STATUS_v0: ACTIVE_LEAN_PROOF_DEBT_LEDGER_KICKOFF",
        "WS10_REMEDIATION_PHASE_C_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_22_DECLARATION_20260405_v0.md",
        "WS10_REMEDIATION_PHASE_C_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_lean_proof_debt_ledger_checkpoint_20260405_v0.json",
        "WS10_REMEDIATION_PHASE_C_GATE_v0: formal/python/tests/test_ws10_t22_lean_proof_debt_ledger_gate.py",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase C token(s): " + ", ".join(missing)


def test_ws10_t22_checkpoint_schema_and_sequence() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "ws10_lean_proof_debt_ledger_checkpoint_20260405_v0"
    assert artifact["status"] == "ACTIVE_LEAN_PROOF_DEBT_LEDGER_KICKOFF"
    assert artifact["anchored_commit"] == "269cd81"

    assert artifact["a1_sequence"] == [
        "formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean",
        "formal/toe_formal/ToeFormal/Bridges/BR01_DispersionToMetric.lean",
        "formal/toe_formal/ToeFormal/Constraints/CT01_Abstract.lean",
    ]
    assert artifact["a2_sequence"] == [
        "formal/toe_formal/ToeFormal/Derivation/Bridges/B4_CRFT_to_AcousticMetric.lean",
        "formal/toe_formal/ToeFormal/Derivation/Bridges/B1_P1_to_UCFF_FirstOrderDispersion.lean",
    ]
    assert artifact["a3_sequence"] == [
        "formal/toe_formal/ToeFormal/Derivation/Bridges/B2_P2_to_UCFF_SecondOrderTimeDomain.lean",
        "formal/toe_formal/ToeFormal/Derivation/Bridges/B3_P2_to_UCFF_SecondOrderNumerics.lean",
    ]

    invariance = artifact.get("invariance", {})
    assert invariance.get("release_gate_truth_invariance") == "ENFORCED"
    assert invariance.get("packet42_policy_invariance") == "ENFORCED"
    assert invariance.get("nonclaim_boundary_invariance") == "ENFORCED"
    assert invariance.get("scalar_freeze_policy_invariance") == "ENFORCED"
