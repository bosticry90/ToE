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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_24_DECLARATION_20260405_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t24_phase_e_preauthorization_checkpoint_20260405_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t24_phase_e_preauthorization_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t24_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 24 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing Tranche 24 checkpoint artifact."
    assert GATE_PATH.exists(), "Missing Tranche 24 gate file."


def test_ws10_t24_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE_PHASE_E_PREAUTHORIZATION_NONCLAIM",
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_24_DECLARATION_20260405_v0.md",
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t24_phase_e_preauthorization_checkpoint_20260405_v0.json",
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_GATE_v0: formal/python/tests/test_ws10_t24_phase_e_preauthorization_gate.py",
        "THEORY_RESTART_T24_REMEDIATION_PHASE_E_ENTRY_CRITERIA_v0: REQUIRES_T23_LOCK_PLUS_BOUNDED_DECLARATION_PLUS_FULL_ACCEPTANCE_LADDER_PASS",
        "THEORY_RESTART_T24_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t24_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_D_STATUS_v0: LOCKED_T21_STASH_INTAKE_ARTIFACTIZATION_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE_PHASE_E_PREAUTHORIZATION_NONCLAIM",
        "WS10_REMEDIATION_PHASE_E_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_24_DECLARATION_20260405_v0.md",
        "WS10_REMEDIATION_PHASE_E_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t24_phase_e_preauthorization_checkpoint_20260405_v0.json",
        "WS10_REMEDIATION_PHASE_E_GATE_v0: formal/python/tests/test_ws10_t24_phase_e_preauthorization_gate.py",
        "WS10_REMEDIATION_PHASE_E_ENTRY_CRITERIA_v0: REQUIRES_T23_LOCK_PLUS_BOUNDED_DECLARATION_PLUS_FULL_ACCEPTANCE_LADDER_PASS",
        "WS10_REMEDIATION_PHASE_E_ADJUDICATION_v0: PREAUTH_CRITERIA_PINNED_NONCLAIM",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase E token(s): " + ", ".join(missing)


def test_ws10_t24_checkpoint_schema() -> None:
    payload = _json(CHECKPOINT_PATH)
    assert payload.get("artifact_id") == "ws10_t24_phase_e_preauthorization_checkpoint_20260405_v0"
    assert payload.get("status") == "ACTIVE_PHASE_E_PREAUTHORIZATION_NONCLAIM"
    assert payload.get("anchored_commit") == "ec19bf7"
    assert payload.get("phase") == "E"
    assert (
        payload.get("entry_criteria")
        == "REQUIRES_T23_LOCK_PLUS_BOUNDED_DECLARATION_PLUS_FULL_ACCEPTANCE_LADDER_PASS"
    )

    preconditions = payload.get("required_preconditions", [])
    assert (
        "WS10_REMEDIATION_PHASE_D_STATUS_v0: LOCKED_T21_STASH_INTAKE_ARTIFACTIZATION_NONLIVE"
        in preconditions
    )
    assert "formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_24_DECLARATION_20260405_v0.md" in preconditions
    assert "formal/python/tests/test_ws10_t24_phase_e_preauthorization_gate.py" in preconditions

    scope = payload.get("allowed_lane_scope", [])
    assert "A1_GR_QM_SEAM_PROMOTION" in scope
    assert "A1_BR01_DISPERSION_TO_METRIC" in scope
    assert "A1_CT01_ABSTRACT_CONSTRAINT" in scope

    invariance = payload.get("invariance", {})
    assert invariance.get("release_gate_truth_invariance") == "ENFORCED"
    assert invariance.get("packet42_policy_invariance") == "ENFORCED"
    assert invariance.get("nonclaim_boundary_invariance") == "ENFORCED"
    assert invariance.get("scalar_freeze_policy_invariance") == "ENFORCED"
