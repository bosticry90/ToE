from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

DOC_REL = "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md"
ARTIFACT_REL = "formal/output/gr_empirical_comparison_packet_05_v0.json"
GATE_REL = "formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py"
SCHEMA_GATE_REL = "formal/python/tests/test_gr_empirical_packet_05_artifact_schema_gate.py"

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


def test_gr_empirical_packet_05_artifact_schema_gate() -> None:
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert artifact.get("schema_id") == "TOE_EMPIRICAL_PACKET_SCHEMA_v0"
    assert artifact.get("artifact_id") == "gr_empirical_comparison_packet_05_v0"
    assert REQUIRED_PAYLOAD_KEYS.issubset(set(payload.keys()))

    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") == "RETAIN_v0"
    assert payload.get("decision_basis") == "packet05_lane_override_retain_survivor_guard_and_prune_signal_v0"
    assert payload.get("decision_record_pointer") == "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_DECISION_RECORD_v0.md"
    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"
    assert payload.get("falsification_surface_pointer") == "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md"
    assert payload.get("falsification_hook") == "WEAK_FIELD_POISSON_RESIDUAL_SIGN_OR_SCALE_FAILURE"
    assert payload.get("maturity_guardrail") == "PHASE5_CLOSEOUT_POSTURE_PRESERVED_v0"
    assert payload.get("override_criteria_pointer") == "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_OVERRIDE_CRITERIA_v0.md"

    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (DOC_REL, ARTIFACT_REL, GATE_REL, SCHEMA_GATE_REL):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
