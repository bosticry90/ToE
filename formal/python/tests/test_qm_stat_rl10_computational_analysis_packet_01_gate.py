from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qm_stat_rl10_computational_analysis_packet_01_gate() -> None:
    doc_text = _read(DOC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    payload = artifact.get("payload", {})

    assert artifact.get("artifact_id") == "qm_stat_rl10_computational_analysis_packet_01_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("authorization_class") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert payload.get("decision") == "INCONCLUSIVE_v0"
    assert payload.get("evidence_tier") == "SCAFFOLD_v0"
    assert payload.get("stability_classification") in {"STABLE_v0", "UNSTABLE_v0", "COMPARATOR_SENSITIVE_v0", "COMPARATOR_INSENSITIVE_v0"}
    assert payload.get("discriminator_classification") in {"DISCRIMINATIVE_v0", "NONDISCRIMINATIVE_v0", "COMPARATOR_SENSITIVE_v0", "COMPARATOR_INSENSITIVE_v0"}

    for field in (
        "assumptions",
        "model_object_pointer",
        "interface_pointer",
        "observable_bundle",
        "discriminator",
        "stop_condition",
        "classification_rule",
        "bounded_output_note",
    ):
        assert payload.get(field), f"Missing payload field `{field}`."

    assert _extract_token(doc_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_AUTHORIZATION_CLASS_v0") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert _extract_token(doc_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_v0") == "INCONCLUSIVE_v0"
    assert _extract_token(doc_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_ARTIFACT_v0") == "qm_stat_rl10_computational_analysis_packet_01_v0"
    assert _extract_token(doc_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_GATE_v0") == "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    plan_text = _read(PLAN_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md",
        "formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_gate.py",
        "formal/output/qm_stat_rl10_computational_analysis_packet_01_v0.json",
    ):
        assert ref in roadmap_text, f"Roadmap must pin `{ref}`."
        assert ref in state_text, f"State must pin `{ref}`."
        assert ref in plan_text, f"Execution plan must pin `{ref}`."

    assert "INV-PHYS-QM-STAT-RL10-COMP-ANALYSIS-PACKET01-v0" in inventory_text
    assert "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS" in inventory_text