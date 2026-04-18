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
EM_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "em_m2_completion_promotion_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "em_m2_completion_promotion_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
ROW_KEYS = (
    "analytic_completeness",
    "canonical_equivalence",
    "assumption_minimization",
    "literature_alignment",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_em_m2_completion_promotion_cycle01_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    em_text = _read(EM_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    em_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-EM"), None)
    assert em_row is not None, "Missing PILLAR-EM row in deep maturity registry."
    assert em_row.get("m2_status") == "COMPLETE_BOUNDED_v0"

    m2_rows = em_row.get("m2_exit_rows", {})
    for key in ROW_KEYS:
        row = m2_rows.get(key)
        assert isinstance(row, dict), f"Missing EM M2 row `{key}`."
        assert row.get("token_value") == "RUN_BOUNDED_v0_NONCLAIM", f"EM M2 row `{key}` must be active bounded-run."

    assert ARTIFACT_PATH.exists(), "EM M2 completion promotion artifact is missing."
    artifact_json = _read_json(ARTIFACT_PATH)
    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert isinstance(artifact_json.get("payload"), dict)
    expected_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == expected_sha

    assert _extract_token(em_text, "EM_M2_STATUS_v0") == "COMPLETE_BOUNDED_v0"
    assert _extract_token(state_text, "EM_M2_STATUS_v0") == "COMPLETE_BOUNDED_v0"
    assert _extract_token(roadmap_text, "EM_M2_STATUS_v0") == "COMPLETE_BOUNDED_v0"

    assert _extract_token(em_text, "EM_M2_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(state_text, "EM_M2_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(roadmap_text, "EM_M2_COMPLETION_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID

    assert _extract_token(em_text, "EM_M2_COMPLETION_SHA256_v0") == expected_sha
    assert _extract_token(state_text, "EM_M2_COMPLETION_SHA256_v0") == expected_sha
    assert _extract_token(roadmap_text, "EM_M2_COMPLETION_SHA256_v0") == expected_sha

    assert _extract_token(em_text, "EM_M2_COMPLETION_GATE_v0") == EXPECTED_GATE
    assert _extract_token(state_text, "EM_M2_COMPLETION_GATE_v0") == EXPECTED_GATE
    assert _extract_token(roadmap_text, "EM_M2_COMPLETION_GATE_v0") == EXPECTED_GATE

    artifact_rel = "formal/output/em_m2_completion_promotion_cycle01_v0.json"
    assert artifact_rel in em_text
    assert artifact_rel in state_text
    assert artifact_rel in roadmap_text

