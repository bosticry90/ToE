from __future__ import annotations

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
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_EMPIRICAL_COMPARISON_PACKET_01_v0.md"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_empirical_comparison_packet_01_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

EXPECTED_ARTIFACT_ID = "toe_empirical_comparison_packet_01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
ALLOWED_DECISIONS = {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_toe_empirical_packet_01_gate() -> None:
    doc_text = _read(DOC_PATH)
    protocol_text = _read(PROTOCOL_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    assert ARTIFACT_PATH.exists(), "Empirical packet-01 artifact is missing."
    artifact_json = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    payload = artifact_json.get("payload")
    assert isinstance(payload, dict)
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") in ALLOWED_DECISIONS

    for field in (
        "artifact_pointer",
        "bridge_pointer",
        "prediction_pointer",
        "discriminator_output_pointer",
        "uncertainty_annotation",
        "bounded_validity_window",
    ):
        assert isinstance(payload.get(field), str) and payload.get(field), f"Missing payload field `{field}`."

    assert _extract_token(doc_text, "TOE_EMPIRICAL_PACKET_01_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "TOE_EMPIRICAL_PACKET_01_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(doc_text, "TOE_EMPIRICAL_PACKET_01_GATE_v0") == EXPECTED_GATE
    assert _extract_token(doc_text, "TOE_EMPIRICAL_PACKET_01_DECISION_v0") in ALLOWED_DECISIONS

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_DECISION_SET_v0") == "RETAIN_PRUNE_INCONCLUSIVE_ONLY"

    for path_ref in (
        "formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_TOE_EMPIRICAL_COMPARISON_PACKET_01_v0.md",
        "formal/python/tests/test_toe_empirical_comparison_packet_01_gate.py",
    ):
        assert path_ref in roadmap_text, f"Roadmap must pin `{path_ref}`."
        assert path_ref in state_text, f"State must pin `{path_ref}`."
