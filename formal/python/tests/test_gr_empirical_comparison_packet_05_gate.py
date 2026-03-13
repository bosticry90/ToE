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
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_gr_empirical_comparison_packet_05_gate() -> None:
    text = _read(DOC_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert "GR_EMPIRICAL_PACKET_05_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM" in text
    assert "GR_EMPIRICAL_PACKET_05_ARTIFACT_v0: gr_empirical_comparison_packet_05_v0" in text
    assert "GR_EMPIRICAL_PACKET_05_DECISION_v0: RETAIN_v0" in text
    assert "formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py" in text

    assert artifact.get("schema_id") == "TOE_EMPIRICAL_PACKET_SCHEMA_v0"
    assert artifact.get("artifact_id") == "gr_empirical_comparison_packet_05_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") == "RETAIN_v0"
    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"
