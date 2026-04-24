from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_01_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_empirical_comparison_packet_01_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qm_empirical_comparison_packet_01_gate() -> None:
    doc_text = _read(DOC_PATH)
    artifact = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))
    payload = artifact.get("payload", {})

    assert artifact.get("artifact_id") == "qm_empirical_comparison_packet_01_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}

    for field in (
        "artifact_pointer",
        "bridge_pointer",
        "prediction_pointer",
        "discriminator_output_pointer",
        "uncertainty_annotation",
        "bounded_validity_window",
    ):
        assert isinstance(payload.get(field), str) and payload.get(field)

    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_01_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_01_ARTIFACT_v0") == "qm_empirical_comparison_packet_01_v0"
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_01_GATE_v0") == "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_01_v0.md",
        "formal/python/tests/test_qm_empirical_comparison_packet_01_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
