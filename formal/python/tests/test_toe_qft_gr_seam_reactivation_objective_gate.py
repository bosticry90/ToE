from __future__ import annotations

import json
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
OBJECTIVE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qft_gr_seam_reactivation_objective_document_structure() -> None:
    text = _read(OBJECTIVE_DOC_PATH)
    required_markers = [
        "Objective ID:",
        "Target ID:",
        "Objective lock tokens:",
        "Active seam question:",
        "Bounded packet family:",
        "Success criteria:",
        "Failure or stop conditions:",
        "Scalar freeze contract (read-only unless forced correction):",
        "Seam governance posture:",
        "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_STATUS_v0: ACTIVE_BOUNDED_OBJECTIVE_LOCKED",
        "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_ARTIFACT_v0: toe_qft_gr_seam_reactivation_objective_checkpoint_v0",
        "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_GATE_v0: REQUIRED_OBJECTIVE_SCHEMA_AND_AUTHORITY_PARITY",
    ]
    for marker in required_markers:
        assert marker in text, f"Seam reactivation objective missing marker: {marker}"


def test_qft_gr_seam_reactivation_objective_checkpoint_schema() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_reactivation_objective_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_0_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_LOCK"
    assert artifact.get("status") == "OBJECTIVE_LOCKED_PENDING_PACKET06_BOUNDARY_CHECK_v0"

    payload = artifact.get("payload", {})
    assert payload.get("objective_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
    assert payload.get("scalar_freeze_doc_path") == "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0.md"
    assert payload.get("scalar_freeze_checkpoint_path") == (
        "formal/output/toe_qft_scalar_route_technical_signoff_checkpoint_v0.json"
    )

    assert isinstance(payload.get("success_criteria"), list) and len(payload.get("success_criteria")) >= 3
    assert isinstance(payload.get("stop_conditions"), list) and len(payload.get("stop_conditions")) >= 3

    governance = payload.get("governance", {})
    assert governance.get("objective_status") == "ACTIVE_BOUNDED_OBJECTIVE_LOCKED"
    assert governance.get("seam_fork_decision_status") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def test_qft_gr_seam_reactivation_objective_authority_parity_and_hold_invariance() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md",
        "formal/output/toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_reactivation_objective_gate.py",
    ]
    for ref in refs:
        assert ref in state_text, f"Missing seam objective pointer in State_of_the_Theory.md: {ref}"
        assert ref in roadmap_text, f"Missing seam objective pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_obj = _extract_token(state_text, "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_STATUS_v0")
    roadmap_obj = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_STATUS_v0")
    assert state_obj == roadmap_obj == "ACTIVE_BOUNDED_OBJECTIVE_LOCKED"

    state_seam = _extract_token(state_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
