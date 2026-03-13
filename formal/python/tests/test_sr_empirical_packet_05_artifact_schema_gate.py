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
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "sr_empirical_comparison_packet_05_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

DOC_REL = "formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_05_v0.md"
ARTIFACT_REL = "formal/output/sr_empirical_comparison_packet_05_v0.json"
GATE_REL = "formal/python/tests/test_sr_empirical_comparison_packet_05_gate.py"
SCHEMA_GATE_REL = "formal/python/tests/test_sr_empirical_packet_05_artifact_schema_gate.py"

REQUIRED_PAYLOAD_KEYS = {
    "status",
    "decision",
    "decision_basis",
    "decision_record_pointer",
    "artifact_pointer",
    "bridge_pointer",
    "prediction_pointer",
    "discriminator_output_pointer",
    "falsification_surface_pointer",
    "falsification_hook",
    "uncertainty_annotation",
    "bounded_validity_window",
    "evidence_tier",
    "maturity_guardrail",
    "override_criteria_pointer",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_sr_empirical_packet_05_artifact_schema_gate() -> None:
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert artifact.get("schema_id") == "TOE_EMPIRICAL_PACKET_SCHEMA_v0"
    assert artifact.get("artifact_id") == "sr_empirical_comparison_packet_05_v0"
    assert REQUIRED_PAYLOAD_KEYS.issubset(set(payload.keys()))

    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") == "RETAIN_v0"
    assert payload.get("decision_basis") == "packet05_lane_override_retain_survivor_guard_and_prune_signal_v0"
    assert payload.get("decision_record_pointer") == "formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_DECISION_RECORD_v0.md"
    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"
    assert payload.get("falsification_surface_pointer") == "formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md"
    assert payload.get("falsification_hook") == "COVARIANCE_DISCRIMINATOR_DRIFT_EXCEEDS_BOUNDED_TOLERANCE"
    assert payload.get("maturity_guardrail") == "PHASE5_CLOSEOUT_POSTURE_PRESERVED_v0"
    assert payload.get("override_criteria_pointer") == "formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_OVERRIDE_CRITERIA_v0.md"

    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    for text in (state_text, roadmap_text):
        assert DOC_REL in text
        assert ARTIFACT_REL in text
        assert GATE_REL in text
        assert SCHEMA_GATE_REL in text
