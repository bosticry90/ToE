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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_23_DECLARATION_20260405_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t23_stash_intake_checkpoint_20260405_v0.json"
PATCH_PATH = REPO_ROOT / "formal" / "output" / "ws10_t23_t21_boundary_overflow_patch_20260405.diff"
MANIFEST_PATH = REPO_ROOT / "formal" / "output" / "ws10_t23_t21_boundary_overflow_manifest_20260405.txt"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t23_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 23 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing Tranche 23 checkpoint artifact."
    assert PATCH_PATH.exists(), "Missing Tranche 23 patch artifact."
    assert MANIFEST_PATH.exists(), "Missing Tranche 23 manifest artifact."


def test_ws10_t23_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_STATUS_v0: LOCKED_T21_STASH_INTAKE_ARTIFACTIZATION_NONLIVE",
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_23_DECLARATION_20260405_v0.md",
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t23_stash_intake_checkpoint_20260405_v0.json",
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_PATCH_ARTIFACT_v0: formal/output/ws10_t23_t21_boundary_overflow_patch_20260405.diff",
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_MANIFEST_ARTIFACT_v0: formal/output/ws10_t23_t21_boundary_overflow_manifest_20260405.txt",
        "THEORY_RESTART_T23_REMEDIATION_PHASE_D_GATE_v0: formal/python/tests/test_ws10_t23_stash_intake_gate.py",
        "THEORY_RESTART_T23_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t23_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_D_STATUS_v0: LOCKED_T21_STASH_INTAKE_ARTIFACTIZATION_NONLIVE",
        "WS10_REMEDIATION_PHASE_D_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_23_DECLARATION_20260405_v0.md",
        "WS10_REMEDIATION_PHASE_D_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t23_stash_intake_checkpoint_20260405_v0.json",
        "WS10_REMEDIATION_PHASE_D_PATCH_ARTIFACT_v0: formal/output/ws10_t23_t21_boundary_overflow_patch_20260405.diff",
        "WS10_REMEDIATION_PHASE_D_MANIFEST_ARTIFACT_v0: formal/output/ws10_t23_t21_boundary_overflow_manifest_20260405.txt",
        "WS10_REMEDIATION_PHASE_D_GATE_v0: formal/python/tests/test_ws10_t23_stash_intake_gate.py",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase D token(s): " + ", ".join(missing)


def test_ws10_t23_checkpoint_schema() -> None:
    payload = _json(CHECKPOINT_PATH)
    assert payload.get("artifact_id") == "ws10_t23_stash_intake_checkpoint_20260405_v0"
    assert payload.get("status") == "LOCKED_T21_STASH_INTAKE_ARTIFACTIZATION_NONLIVE"
    assert payload.get("anchored_commit") == "7730c32"
    assert payload.get("source_stash_label") == "temp-ws10-t21-out-of-bound-hygiene"
    assert payload.get("patch_artifact") == "formal/output/ws10_t23_t21_boundary_overflow_patch_20260405.diff"
    assert payload.get("manifest_artifact") == "formal/output/ws10_t23_t21_boundary_overflow_manifest_20260405.txt"

    files = payload.get("captured_files", [])
    assert "GOVERNANCE_VERSION_v2.lock" in files
    assert "formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_21_DECLARATION_20260404_v0.md" in files
    assert "formal/python/tests/test_ws10_t21_authority_ownership_enforcement_gate.py" in files
    assert "formal/python/tests/test_ws10_t21_authority_residency_parity_gate.py" in files

    invariance = payload.get("invariance", {})
    assert invariance.get("release_gate_truth_invariance") == "ENFORCED"
    assert invariance.get("packet42_policy_invariance") == "ENFORCED"
    assert invariance.get("nonclaim_boundary_invariance") == "ENFORCED"
    assert invariance.get("scalar_freeze_policy_invariance") == "ENFORCED"
