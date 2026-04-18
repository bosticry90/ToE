from __future__ import annotations

import hashlib
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_DISCRIMINATOR_EMP_QM_01_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_empirical_discriminator_emp_qm_01_run_cycle02_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert match is not None, f"Missing token `{token_name}`."
    return match.group(1)


def test_qm_emp_qm_01_run_bundle_is_hash_and_pointer_pinned() -> None:
    doc_text = _read(DOC_PATH)
    artifact_bytes = ARTIFACT_PATH.read_bytes()
    artifact_hash = hashlib.sha256(artifact_bytes).hexdigest()

    assert _extract_token(doc_text, "EMP_QM_01_DISCRIMINATOR_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "EMP_QM_01_PRUNE_DECISION_v0") == "ELIMINATION_READY_BOUNDED_v0"
    assert _extract_token(doc_text, "EMP_QM_01_PRUNE_RESULT_v0") == "PASS_AND_PRUNE_SIGNAL_PRESENT_v0"
    assert _extract_token(doc_text, "EMP_QM_01_ARTIFACT_v0") == "qm_empirical_discriminator_emp_qm_01_run_cycle02_v0"
    assert _extract_token(doc_text, "EMP_QM_01_GATE_v0") == "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
    assert _extract_token(doc_text, "EMP_QM_01_ARTIFACT_SHA256_v0") == artifact_hash

    for path_ref in (
        "formal/output/qm_empirical_discriminator_emp_qm_01_run_cycle02_v0.json",
        "formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py",
        "formal/docs/lanes/OV-DR-BR-01_dr01_to_br01_eliminative_lane.md",
    ):
        assert path_ref in doc_text, f"QM discriminator doc must pin `{path_ref}`."

    artifact_text = ARTIFACT_PATH.read_text(encoding="utf-8")
    assert '"candidate_elimination_ready": true' in artifact_text
    assert '"prune_decision": "PASS_AND_PRUNE_SIGNAL_PRESENT_v0"' in artifact_text
    assert '"pruned_candidate_families"' in artifact_text
    assert '"surviving_candidate_families"' in artifact_text


def test_qm_emp_qm_01_cross_surface_pointers_are_present() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for path_ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_DISCRIMINATOR_EMP_QM_01_v0.md",
        "formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py",
    ):
        assert path_ref in roadmap_text, f"Roadmap must pin `{path_ref}`."
        assert path_ref in state_text or path_ref in inventory_text, f"Compact-State or central inventory must pin `{path_ref}`."
