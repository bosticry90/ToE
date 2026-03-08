from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
GR_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_COMPLETENESS_GATE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_m2_canonical_equivalence_scaffold_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "gr_m2_canonical_equivalence_scaffold_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_gr_m2_canonical_equivalence_scaffold_cycle01_gate() -> None:
    gr_text = _read(GR_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert ARTIFACT_PATH.exists(), "GR M2 canonical equivalence scaffold artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert isinstance(artifact_json.get("payload"), dict)
    expected_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == expected_sha

    assert _extract_token(gr_text, "GR_M2_CANONICAL_EQUIVALENCE_STATUS_v0") == "SCAFFOLD_PINNED_NONCLAIM"
    assert _extract_token(state_text, "GR_M2_CANONICAL_EQUIVALENCE_STATUS_v0") == "SCAFFOLD_PINNED_NONCLAIM"
    assert _extract_token(roadmap_text, "GR_M2_CANONICAL_EQUIVALENCE_STATUS_v0") == "SCAFFOLD_PINNED_NONCLAIM"

    assert _extract_token(gr_text, "GR_M2_CANONICAL_EQUIVALENCE_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(state_text, "GR_M2_CANONICAL_EQUIVALENCE_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(roadmap_text, "GR_M2_CANONICAL_EQUIVALENCE_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID

    assert _extract_token(gr_text, "GR_M2_CANONICAL_EQUIVALENCE_SHA256_v0") == expected_sha
    assert _extract_token(state_text, "GR_M2_CANONICAL_EQUIVALENCE_SHA256_v0") == expected_sha
    assert _extract_token(roadmap_text, "GR_M2_CANONICAL_EQUIVALENCE_SHA256_v0") == expected_sha

    assert _extract_token(gr_text, "GR_M2_CANONICAL_EQUIVALENCE_GATE_v0") == EXPECTED_GATE
    assert _extract_token(state_text, "GR_M2_CANONICAL_EQUIVALENCE_GATE_v0") == EXPECTED_GATE
    assert _extract_token(roadmap_text, "GR_M2_CANONICAL_EQUIVALENCE_GATE_v0") == EXPECTED_GATE

    artifact_rel = "formal/output/gr_m2_canonical_equivalence_scaffold_cycle01_v0.json"
    assert artifact_rel in gr_text
    assert artifact_rel in state_text
    assert artifact_rel in roadmap_text
