from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "ws10_remediation_baseline_snapshot_20260404_v0.json"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_20_DECLARATION_20260404_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t20_kickoff_artifacts_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert ARTIFACT_PATH.exists(), "Missing remediation baseline snapshot artifact."
    assert DECLARATION_PATH.exists(), "Missing Tranche 20 declaration."


def test_ws10_t20_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PROGRAM_ADJUDICATION_v0: LOCKED_PHASE_A_KICKOFF",
        "REMEDIATION_RELEASE_GATE_TRUTH_INVARIANCE_v0: ENFORCED",
        "REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
        "REMEDIATION_NONCLAIM_BOUNDARY_INVARIANCE_v0: ENFORCED",
        "REMEDIATION_SCALAR_FREEZE_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program token(s): " + ", ".join(missing)


def test_ws10_t20_baseline_artifact_schema() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "ws10_remediation_baseline_snapshot_20260404_v0"
    assert artifact["status"] == "LOCKED_PHASE_A_KICKOFF"
    assert artifact["anchored_commit"] == "95def34"
    assert artifact["baseline_envelope"]["clean_tree_required"] is True


def test_ws10_t20_authority_parity_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T20_REMEDIATION_PROGRAM_STATUS_v0: LOCKED_PHASE_A_KICKOFF",
        "THEORY_RESTART_T20_REMEDIATION_PROGRAM_ARTIFACT_v0: formal/output/ws10_remediation_baseline_snapshot_20260404_v0.json",
        "THEORY_RESTART_T20_REMEDIATION_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T20_REMEDIATION_PROGRAM_GATE_v0: formal/python/tests/test_ws10_t20_remediation_kickoff_gate.py",
        "THEORY_RESTART_T20_REMEDIATION_RELEASE_GATE_TRUTH_INVARIANCE_v0: ENFORCED",
        "THEORY_RESTART_T20_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"
