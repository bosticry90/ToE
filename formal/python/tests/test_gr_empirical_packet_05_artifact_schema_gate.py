from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

DOC_REL = "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md"
ARTIFACT_REL = "formal/output/gr_empirical_comparison_packet_05_v0.json"
GATE_REL = "formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py"
SCHEMA_GATE_REL = "formal/python/tests/test_gr_empirical_packet_05_artifact_schema_gate.py"

REQUIRED_PAYLOAD_KEYS = {
    "status",
    "decision",
    "artifact_pointer",
    "bridge_pointer",
    "prediction_pointer",
    "discriminator_output_pointer",
    "uncertainty_annotation",
    "bounded_validity_window",
    "evidence_tier",
    "maturity_guardrail",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_gr_empirical_packet_05_artifact_schema_gate() -> None:
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert artifact.get("schema_id") == "TOE_EMPIRICAL_PACKET_SCHEMA_v0"
    assert artifact.get("artifact_id") == "gr_empirical_comparison_packet_05_v0"
    assert REQUIRED_PAYLOAD_KEYS.issubset(set(payload.keys()))

    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") == "INCONCLUSIVE_v0"
    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"
    assert payload.get("maturity_guardrail") == "PHASE5_CLOSEOUT_POSTURE_PRESERVED_v0"

    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    for text in (state_text, roadmap_text):
        assert DOC_REL in text
        assert ARTIFACT_REL in text
        assert GATE_REL in text
        assert SCHEMA_GATE_REL in text
