from __future__ import annotations

import hashlib
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHASE3_M3_CONSOLIDATION_PROMOTION_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "phase3_m3_consolidation_promotion_cycle01_v0.json"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_PROGRAM_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert match is not None, f"Missing token `{token_name}`."
    return match.group(1)


def test_phase3_m3_consolidation_bundle_is_hash_and_pointer_pinned() -> None:
    doc_text = _read(DOC_PATH)
    artifact_bytes = ARTIFACT_PATH.read_bytes()
    artifact_hash = hashlib.sha256(artifact_bytes).hexdigest()

    assert _extract_token(doc_text, "PHASE3_M3_CONSOLIDATION_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "PHASE3_M3_CONSOLIDATION_READINESS_v0") == "READY_FOR_M4_SEAM_CLOSURE_PROMOTION_v0"
    assert _extract_token(doc_text, "PHASE3_M3_CONSOLIDATION_ARTIFACT_v0") == "phase3_m3_consolidation_promotion_cycle01_v0"
    assert _extract_token(doc_text, "PHASE3_M3_CONSOLIDATION_GATE_v0") == "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
    assert _extract_token(doc_text, "PHASE3_M3_CONSOLIDATION_ARTIFACT_SHA256_v0") == artifact_hash

    for path_ref in (
        "formal/output/phase3_m3_consolidation_promotion_cycle01_v0.json",
        "formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py",
        "formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md",
        "formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json",
    ):
        assert path_ref in doc_text, f"Consolidation doc must pin `{path_ref}`."


def test_phase3_m3_consolidation_cross_surface_pointers_are_present() -> None:
    program_text = _read(PROGRAM_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for path_ref in (
        "formal/docs/release/PHASE3_M3_CONSOLIDATION_PROMOTION_v0.md",
        "formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py",
    ):
        assert path_ref in program_text, f"Program must pin `{path_ref}`."
        assert path_ref in roadmap_text, f"Roadmap must pin `{path_ref}`."
        assert path_ref in state_text, f"State must pin `{path_ref}`."
