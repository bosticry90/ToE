from __future__ import annotations

import hashlib
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
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
TARGET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md"
GR_AUTHORITY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_COMPLETENESS_GATE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_m3_completion_promotion_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "gr_m3_completion_promotion_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_gr_m3_completion_promotion_cycle01_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    target_text = _read(TARGET_DOC_PATH)
    gr_text = _read(GR_AUTHORITY_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert ARTIFACT_PATH.exists(), "GR M3 completion promotion artifact is missing."
    artifact_json = _read_json(ARTIFACT_PATH)
    artifact_hash = hashlib.sha256(ARTIFACT_PATH.read_bytes()).hexdigest()

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("payload", {}).get("status") == "COMPLETE_BOUNDED_v0"
    assert artifact_json.get("payload", {}).get("promotion_readiness") == "FIRST_DISCRIMINATOR_CLOSED_AND_PROMOTED_v0"

    gr_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-GR"), None)
    assert gr_row is not None, "Missing PILLAR-GR row in deep maturity registry."
    assert gr_row.get("m3_status") == "COMPLETE_BOUNDED_v0"

    m3_completion = gr_row.get("m3_completion", {})
    assert m3_completion.get("target_id") == "TARGET-GR-M3-COMPLETION-PROMOTION-v0"
    assert m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md"
    assert m3_completion.get("artifact_path") == "formal/output/gr_m3_completion_promotion_cycle01_v0.json"
    assert m3_completion.get("gate_path") == "formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py"

    for text in (target_text, gr_text, state_text, roadmap_text):
        assert _extract_token(text, "GR_M3_STATUS_v0") == "COMPLETE_BOUNDED_v0"
        assert _extract_token(text, "GR_M3_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
        assert _extract_token(text, "GR_M3_COMPLETION_SHA256_v0") == artifact_hash
        assert _extract_token(text, "GR_M3_COMPLETION_GATE_v0") == EXPECTED_GATE
        assert _extract_token(text, "GR_M3_PROMOTION_READINESS_v0") == "FIRST_DISCRIMINATOR_CLOSED_AND_PROMOTED_v0"

    for path_ref in (
        "formal/output/gr_m3_completion_promotion_cycle01_v0.json",
        "formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md",
    ):
        assert path_ref in target_text
        assert path_ref in gr_text
        assert path_ref in state_text
        assert path_ref in roadmap_text
