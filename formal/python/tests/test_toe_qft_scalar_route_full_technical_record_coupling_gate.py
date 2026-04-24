from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_full_technical_record_checkpoint_v0.json"
MANIFEST_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_scalar_inventory_manifest_v0.json"

EXPECTED_STATUS = "PHASE0_PHASE1_LOCKED_AUDIT_READY_V0"
EXPECTED_COUPLING_STATUS = "ARTIFACT_AND_STATUS_PARITY_ENFORCED"
EXPECTED_SEAM_HOLD = "HOLD_FOR_SCALAR_PUBLICATION_v0"
EXPECTED_CHECKPOINT_FILE = "toe_qft_scalar_route_full_technical_record_checkpoint_v0.json"
EXPECTED_MANIFEST_FILE = "toe_qft_scalar_route_scalar_inventory_manifest_v0.json"

REQUIRED_REFS = (
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md",
    "formal/output/toe_qft_scalar_route_full_technical_record_checkpoint_v0.json",
    "formal/output/toe_qft_scalar_route_scalar_inventory_manifest_v0.json",
    "formal/python/tests/test_toe_qft_scalar_route_full_technical_record_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_full_technical_record_coupling_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_scalar_full_technical_record_cross_surface_ref_parity() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in REQUIRED_REFS:
        assert ref in state_text, f"Missing full-technical-record pointer from State_of_the_Theory.md: {ref}"
        assert ref in roadmap_text, f"Missing full-technical-record pointer from PHYSICS_ROADMAP_v0.md: {ref}"
        assert (REPO_ROOT / ref).exists(), f"Referenced pointer target does not exist: {ref}"


def test_scalar_full_technical_record_status_and_file_tokens_match_across_surfaces() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    state_status = _extract_token(state_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_STATUS_v0")
    roadmap_status = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_STATUS_v0")
    state_coupling = _extract_token(state_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_COUPLING_STATUS_v0")
    roadmap_coupling = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_COUPLING_STATUS_v0")

    state_checkpoint_file = _extract_token(state_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_CHECKPOINT_FILE_v0")
    roadmap_checkpoint_file = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_CHECKPOINT_FILE_v0")
    state_manifest_file = _extract_token(state_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_FILE_v0")
    roadmap_manifest_file = _extract_token(roadmap_text, "SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_FILE_v0")

    assert state_status == roadmap_status == EXPECTED_STATUS
    assert state_coupling == roadmap_coupling == EXPECTED_COUPLING_STATUS

    assert state_checkpoint_file == roadmap_checkpoint_file == EXPECTED_CHECKPOINT_FILE
    assert state_manifest_file == roadmap_manifest_file == EXPECTED_MANIFEST_FILE


def test_scalar_full_technical_record_checkpoint_manifest_match_canonical_files() -> None:
    checkpoint = _read_json(CHECKPOINT_PATH)
    manifest = _read_json(MANIFEST_PATH)

    assert CHECKPOINT_PATH.name == EXPECTED_CHECKPOINT_FILE
    assert MANIFEST_PATH.name == EXPECTED_MANIFEST_FILE

    assert checkpoint.get("artifact_id") == "toe_qft_scalar_route_full_technical_record_checkpoint_v0"
    assert manifest.get("artifact_id") == "toe_qft_scalar_route_scalar_inventory_manifest_v0"


def test_scalar_full_technical_record_seam_hold_posture_unchanged() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    state_seam = _extract_token(state_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")

    assert state_seam == roadmap_seam == EXPECTED_SEAM_HOLD
