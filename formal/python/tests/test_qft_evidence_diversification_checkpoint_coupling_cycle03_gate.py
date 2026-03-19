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
QFT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qft_evidence_diversification_checkpoint_cycle03_v0.json"

EXPECTED_ARTIFACT_ID = "qft_evidence_diversification_checkpoint_cycle03_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_compact_state_or_inventory(state_text: str, inventory_text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", state_text)
    if match is not None:
        return match.group(1)
    inventory_match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", inventory_text)
    assert inventory_match is not None, f"Missing token `{token_name}` in compact state and central inventory."
    return inventory_match.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_qft_evidence_diversification_checkpoint_coupling_cycle03_gate() -> None:
    qft_text = _read(QFT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert ARTIFACT_PATH.exists(), "QFT evidence-diversification cycle-03 checkpoint artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert "payload" in artifact_json and isinstance(artifact_json["payload"], dict)
    assert "payload_sha256" in artifact_json and isinstance(artifact_json["payload_sha256"], str)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json["payload_sha256"] == computed_payload_sha, (
        "QFT evidence-diversification cycle-03 payload_sha256 does not match canonical payload hash."
    )

    qft_artifact_token = _extract_token(qft_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_ARTIFACT_v0")
    state_artifact_token = _extract_token_from_compact_state_or_inventory(state_text, inventory_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_ARTIFACT_v0")
    roadmap_artifact_token = _extract_token(roadmap_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_ARTIFACT_v0")

    qft_sha_token = _extract_token(qft_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_SHA256_v0")
    state_sha_token = _extract_token_from_compact_state_or_inventory(state_text, inventory_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_SHA256_v0")
    roadmap_sha_token = _extract_token(roadmap_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_SHA256_v0")

    qft_gate_token = _extract_token(qft_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_GATE_v0")
    state_gate_token = _extract_token_from_compact_state_or_inventory(state_text, inventory_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_GATE_v0")
    roadmap_gate_token = _extract_token(roadmap_text, "QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_GATE_v0")

    assert qft_artifact_token == roadmap_artifact_token == EXPECTED_ARTIFACT_ID
    assert state_artifact_token == EXPECTED_ARTIFACT_ID
    assert qft_sha_token == roadmap_sha_token == artifact_json["payload_sha256"]
    assert state_sha_token == artifact_json["payload_sha256"]
    assert qft_gate_token == roadmap_gate_token == EXPECTED_COUPLING_GATE
    assert state_gate_token == EXPECTED_COUPLING_GATE

    artifact_rel = "formal/output/qft_evidence_diversification_checkpoint_cycle03_v0.json"
    assert artifact_rel in qft_text
    assert artifact_rel in state_text or artifact_rel in inventory_text
    assert artifact_rel in roadmap_text

    assert "Keep the lane bounded and non-claim while discharge obligations are assembled." in qft_text
    assert "- `QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0`" in qft_text



