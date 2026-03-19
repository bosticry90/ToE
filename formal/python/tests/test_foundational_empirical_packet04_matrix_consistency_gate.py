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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet04_matrix_surface_is_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap = _read(ROADMAP_PATH)
    inventory = _read(INVENTORY_PATH)
    state = _read(STATE_PATH)

    assert matrix.get("matrix_id") == "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0"
    assert matrix.get("matrix_version") == 1
    assert matrix.get("protocol_doc") == "formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
    assert set(matrix.get("allowed_decisions", [])) == {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}

    for ref in (
        "formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0.json",
        "formal/python/tests/test_foundational_empirical_packet04_matrix_consistency_gate.py",
    ):
        assert ref in roadmap
        assert ref in state or ref in inventory


def test_packet04_matrix_rows_pin_next_surface_paths() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and len(rows) == 7

    expected_lanes = {"QM", "GR", "STAT", "COSMO", "EM", "QFT", "SR"}
    assert set(rows.keys()) == expected_lanes

    for lane, row in rows.items():
        doc_path = REPO_ROOT / row["doc_path"]
        artifact_path = REPO_ROOT / row["artifact_path"]
        gate_path = REPO_ROOT / row["gate_path"]

        assert doc_path.exists(), f"{lane}: missing packet-04 doc `{doc_path}`."
        assert artifact_path.exists(), f"{lane}: missing packet-04 artifact `{artifact_path}`."
        assert gate_path.exists(), f"{lane}: missing packet-04 gate `{gate_path}`."

        doc_text = _read(doc_path)
        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})

        assert artifact.get("artifact_id", "").endswith("_packet_04_v0")
        assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
        assert payload.get("decision") in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}
        assert payload.get("decision") == "INCONCLUSIVE_v0"

        assert f"{lane}_EMPIRICAL_PACKET_04_STATUS_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_04_ARTIFACT_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_04_GATE_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_04_DECISION_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_04_EVIDENCE_TIER_v0" in doc_text
