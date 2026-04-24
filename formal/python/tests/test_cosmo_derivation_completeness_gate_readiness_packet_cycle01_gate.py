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
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_derivation_completeness_gate_readiness_packet_cycle01_v0.json"
)

EXPECTED_ARTIFACT_ID = "cosmo_derivation_completeness_gate_readiness_packet_cycle01_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_PACKET_SCOPE = "LOCKED_QUEUE_PREREQUISITES_PINNED_BEFORE_ENTRY"
EXPECTED_ARTIFACT_REL = "formal/output/cosmo_derivation_completeness_gate_readiness_packet_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_cosmo_derivation_completeness_gate_readiness_packet_cycle01_gate.py"


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


def test_cosmo_derivation_completeness_gate_readiness_packet_cycle01_gate() -> None:
    cosmo_text = _read(COSMO_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    suite_text = _read(SUITE_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is True
    assert isinstance(artifact_json.get("payload"), dict)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == computed_payload_sha, (
        "COSMO derivation-completeness gate readiness packet cycle-01 payload_sha256 does not match canonical payload hash."
    )

    for token_name, expected in (
        ("COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_GATE_v0", EXPECTED_COUPLING_GATE),
        ("COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_v0", "PRESENT"),
        ("COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_SCOPE_v0", EXPECTED_PACKET_SCOPE),
    ):
        assert _extract_token(cosmo_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    cosmo_sha = _extract_token(cosmo_text, "COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_SHA256_v0")
    state_sha = _extract_token(state_text, "COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_SHA256_v0")
    roadmap_sha = _extract_token(roadmap_text, "COSMO_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_SHA256_v0")
    assert cosmo_sha == state_sha == roadmap_sha == artifact_json["payload_sha256"]

    for doc_text, doc_label in (
        (cosmo_text, "COSMO parent target"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert EXPECTED_ARTIFACT_REL in doc_text, (
            f"{doc_label} must pin the derivation-completeness readiness packet artifact path."
        )
        assert EXPECTED_GATE_REL in doc_text, (
            f"{doc_label} must pin the derivation-completeness readiness packet gate path."
        )

    payload = artifact_json["payload"]
    assert payload.get("checkpoint") == "cosmo_derivation_completeness_gate_readiness_packet_cycle01"
    assert payload.get("status") == "readiness_packet_non_promotional"
    assert payload.get("discharge_row_linkage") == ["TOE-COSMO-DER-01", "TOE-COSMO-DER-02"]

    assert "- bounded derivation-completeness readiness-input scope only; no derivation-completeness discharge claim and no external truth claim." in cosmo_text
    assert "- readiness packet remains non-promotional and does not authorize `TOE-COSMO-DER-*` label promotion." in cosmo_text

    assert EXPECTED_GATE_REL in suite_text, "governance_suite.ps1 must execute COSMO derivation-completeness readiness packet gate."
