from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
TARGET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md"
STAT_AUTHORITY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CENTRAL_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_m4_seam_closure_promotion_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "stat_m4_seam_closure_promotion_cycle01_v0"
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


def test_stat_m4_seam_closure_promotion_cycle01_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    target_text = _read(TARGET_DOC_PATH)
    stat_text = _read(STAT_AUTHORITY_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    central_inventory_text = _read(CENTRAL_INVENTORY_PATH)

    assert ARTIFACT_PATH.exists(), "STAT M4 seam-closure promotion artifact is missing."
    artifact_json = _read_json(ARTIFACT_PATH)
    artifact_hash = hashlib.sha256(ARTIFACT_PATH.read_bytes()).hexdigest()

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("payload", {}).get("status") == "COMPLETE_BOUNDED_v0"
    assert artifact_json.get("payload", {}).get("promotion_readiness") == "CROSS_PILLAR_SEAM_BUNDLE_PINNED_v0"

    stat_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-STAT"), None)
    assert stat_row is not None, "Missing PILLAR-STAT row in deep maturity registry."
    assert stat_row.get("m4_status") == "COMPLETE_BOUNDED_v0"

    m4_completion = stat_row.get("m4_completion", {})
    assert m4_completion.get("target_id") == "TARGET-STAT-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert m4_completion.get("artifact_path") == "formal/output/stat_m4_seam_closure_promotion_cycle01_v0.json"
    assert m4_completion.get("gate_path") == "formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py"

    for text in (target_text, stat_text, state_text, roadmap_text):
        assert _extract_token(text, "STAT_M4_STATUS_v0") == "COMPLETE_BOUNDED_v0"
        assert _extract_token(text, "STAT_M4_SEAM_CLOSURE_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
        assert _extract_token(text, "STAT_M4_SEAM_CLOSURE_SHA256_v0") == artifact_hash
        assert _extract_token(text, "STAT_M4_SEAM_CLOSURE_GATE_v0") == EXPECTED_GATE
        assert _extract_token(text, "STAT_M4_PROMOTION_READINESS_v0") == "CROSS_PILLAR_SEAM_BUNDLE_PINNED_v0"

    for path_ref in (
        "formal/output/stat_m4_seam_closure_promotion_cycle01_v0.json",
        "formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md",
    ):
        assert path_ref in target_text
        assert path_ref in stat_text
        assert path_ref in state_text or path_ref in central_inventory_text
        assert path_ref in roadmap_text
