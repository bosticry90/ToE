from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_03_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_empirical_comparison_packet_03_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_stat_empirical_comparison_packet_03_gate() -> None:
    text = _read(DOC_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert "STAT_EMPIRICAL_PACKET_03_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM" in text
    assert "STAT_EMPIRICAL_PACKET_03_ARTIFACT_v0: stat_empirical_comparison_packet_03_v0" in text
    assert "STAT_EMPIRICAL_PACKET_03_DECISION_v0: INCONCLUSIVE_v0" in text
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") == "INCONCLUSIVE_v0"
