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
COSMO_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Cosmology" / "BackgroundObjectScaffold.lean"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_der02_governance_coupling_scaffold_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "cosmo_der02_governance_coupling_scaffold_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_ROW_LABEL_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_ROW_BINDING = "TOE_COSMO_DER_02_P_POLICY_GOVERNANCE_COUPLING_SCAFFOLD_PINNED_NONCLAIM"
EXPECTED_ARTIFACT_REL = "formal/output/cosmo_der02_governance_coupling_scaffold_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_cosmo_der02_governance_coupling_scaffold_cycle01_gate.py"


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


def test_cosmo_der02_governance_coupling_scaffold_cycle01_gate() -> None:
    cosmo_text = _read(COSMO_DOC_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    results_text = _read(RESULTS_PATH)
    lean_text = _read(LEAN_PATH)
    suite_text = _read(SUITE_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is False
    assert isinstance(artifact_json.get("payload"), dict)

    payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == payload_sha

    for token_name, expected in (
        ("COSMO_DER02_GOVERNANCE_COUPLING_SCAFFOLD_CYCLE01_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("COSMO_DER02_GOVERNANCE_COUPLING_SCAFFOLD_CYCLE01_GATE_v0", EXPECTED_GATE),
        ("COSMO_DER02_GOVERNANCE_COUPLING_ROW_BINDING_v0", EXPECTED_ROW_BINDING),
    ):
        assert _extract_token(cosmo_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected

    assert _extract_token(cosmo_text, "COSMO_DER02_GOVERNANCE_COUPLING_SCAFFOLD_CYCLE01_SHA256_v0") == payload_sha
    assert _extract_token(roadmap_text, "COSMO_DER02_GOVERNANCE_COUPLING_SCAFFOLD_CYCLE01_SHA256_v0") == payload_sha
    assert _extract_token(state_text, "COSMO_DER02_GOVERNANCE_COUPLING_SCAFFOLD_CYCLE01_SHA256_v0") == payload_sha

    for doc in (cosmo_text, roadmap_text, state_text):
        assert EXPECTED_ARTIFACT_REL in doc
        assert EXPECTED_GATE_REL in doc

    for token in [
        "cosmo_der01_background_surface_scaffold_cycle01_v0",
        "cosmo_der02_governance_coupling_surface_scaffold_cycle01_v0",
        "COSMO_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_POLICY_v0: PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP",
        "COSMO_AUTHORIZED_UNLOCK_CHECKLIST_PACKET_POLICY_v0: CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE",
        "COSMO_DRYRUN_RECONCILIATION_PACKET_POLICY_v0: CYCLE08_09_10_POLICY_COHERENCE_REQUIRED_NO_STATUS_FLIP",
    ]:
        assert token in (json.dumps(artifact_json) if ":" in token else lean_text + json.dumps(artifact_json))

    assert "TOE-COSMO-DER-02" in results_text
    assert "| TOE-COSMO-DER-02 | `P-POLICY` |" in results_text

    assert EXPECTED_GATE_REL in suite_text
