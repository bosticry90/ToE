from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_m2_literature_alignment_scaffold_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "cosmo_m2_literature_alignment_scaffold_cycle01_v0"
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


def test_cosmo_m2_literature_alignment_scaffold_cycle01_gate() -> None:
    cosmo_text = _read(COSMO_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert ARTIFACT_PATH.exists(), "COSMO M2 literature alignment scaffold artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert isinstance(artifact_json.get("payload"), dict)
    expected_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == expected_sha

    assert _extract_token(cosmo_text, "COSMO_M2_LITERATURE_ALIGNMENT_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(state_text, "COSMO_M2_LITERATURE_ALIGNMENT_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(roadmap_text, "COSMO_M2_LITERATURE_ALIGNMENT_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"

    assert _extract_token(cosmo_text, "COSMO_M2_LITERATURE_ALIGNMENT_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(state_text, "COSMO_M2_LITERATURE_ALIGNMENT_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(roadmap_text, "COSMO_M2_LITERATURE_ALIGNMENT_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID

    assert _extract_token(cosmo_text, "COSMO_M2_LITERATURE_ALIGNMENT_SHA256_v0") == expected_sha
    assert _extract_token(state_text, "COSMO_M2_LITERATURE_ALIGNMENT_SHA256_v0") == expected_sha
    assert _extract_token(roadmap_text, "COSMO_M2_LITERATURE_ALIGNMENT_SHA256_v0") == expected_sha

    assert _extract_token(cosmo_text, "COSMO_M2_LITERATURE_ALIGNMENT_GATE_v0") == EXPECTED_GATE
    assert _extract_token(state_text, "COSMO_M2_LITERATURE_ALIGNMENT_GATE_v0") == EXPECTED_GATE
    assert _extract_token(roadmap_text, "COSMO_M2_LITERATURE_ALIGNMENT_GATE_v0") == EXPECTED_GATE

    artifact_rel = "formal/output/cosmo_m2_literature_alignment_scaffold_cycle01_v0.json"
    assert artifact_rel in cosmo_text
    assert artifact_rel in state_text
    assert artifact_rel in roadmap_text
