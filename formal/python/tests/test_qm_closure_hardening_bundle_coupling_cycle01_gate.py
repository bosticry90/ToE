from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QM_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_closure_hardening_bundle_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "qm_closure_hardening_bundle_cycle01_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"


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


def test_qm_closure_hardening_bundle_coupling_cycle01_gate() -> None:
    qm_text = _read(QM_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert ARTIFACT_PATH.exists(), "QM closure-hardening cycle-01 artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert "payload" in artifact_json and isinstance(artifact_json["payload"], dict)
    assert "payload_sha256" in artifact_json and isinstance(artifact_json["payload_sha256"], str)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json["payload_sha256"] == computed_payload_sha, (
        "QM closure-hardening cycle-01 payload_sha256 does not match canonical payload hash."
    )

    qm_artifact_token = _extract_token(qm_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0")
    state_artifact_token = _extract_token(state_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0")
    roadmap_artifact_token = _extract_token(roadmap_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0")

    qm_sha_token = _extract_token(qm_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0")
    state_sha_token = _extract_token(state_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0")
    roadmap_sha_token = _extract_token(roadmap_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0")

    qm_gate_token = _extract_token(qm_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_GATE_v0")
    state_gate_token = _extract_token(state_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_GATE_v0")
    roadmap_gate_token = _extract_token(roadmap_text, "QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_GATE_v0")

    assert qm_artifact_token == state_artifact_token == roadmap_artifact_token == EXPECTED_ARTIFACT_ID
    assert qm_sha_token == state_sha_token == roadmap_sha_token == artifact_json["payload_sha256"]
    assert qm_gate_token == state_gate_token == roadmap_gate_token == EXPECTED_COUPLING_GATE

    artifact_rel = "formal/output/qm_closure_hardening_bundle_cycle01_v0.json"
    assert artifact_rel in qm_text
    assert artifact_rel in state_text
    assert artifact_rel in roadmap_text

    assert "- non-claim boundary remains explicit and binding for this artifact." in qm_text
