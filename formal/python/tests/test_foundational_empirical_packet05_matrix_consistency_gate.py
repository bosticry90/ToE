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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet05_matrix_surface_is_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap = _read(ROADMAP_PATH)
    state = _read(STATE_PATH)

    assert matrix.get("matrix_id") == "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0"
    assert matrix.get("matrix_version") == 1
    assert matrix.get("protocol_doc") == "formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
    assert matrix.get("progression_policy_doc") == "formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0.md"
    assert matrix.get("enabled_lanes") == ["GR", "SR"]

    for ref in (
        "formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json",
        "formal/python/tests/test_foundational_empirical_packet05_matrix_consistency_gate.py",
    ):
        assert ref in roadmap
        assert ref in state


def test_packet05_matrix_rows_pin_lane05_surfaces() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and len(rows) == 2
    assert set(rows.keys()) == {"GR", "SR"}

    for lane, row in rows.items():
        doc_path = REPO_ROOT / row["doc_path"]
        artifact_path = REPO_ROOT / row["artifact_path"]
        gate_path = REPO_ROOT / row["gate_path"]
        schema_gate_path = REPO_ROOT / row["schema_gate_path"]
        override_criteria_path = REPO_ROOT / row["override_criteria_path"]

        assert doc_path.exists(), f"{lane}: missing packet-05 doc `{doc_path}`."
        assert artifact_path.exists(), f"{lane}: missing packet-05 artifact `{artifact_path}`."
        assert gate_path.exists(), f"{lane}: missing packet-05 gate `{gate_path}`."
        assert schema_gate_path.exists(), f"{lane}: missing packet-05 schema gate `{schema_gate_path}`."

        doc_text = _read(doc_path)
        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})

        assert artifact.get("artifact_id", "").endswith("_packet_05_v0")
        assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
        assert payload.get("decision") in {"INCONCLUSIVE_v0", "RETAIN_v0", "PRUNE_v0"}
        assert payload.get("evidence_tier") == "INTERMEDIATE_v0"
        if payload.get("decision") != "INCONCLUSIVE_v0":
            assert override_criteria_path.exists(), f"{lane}: missing packet-05 override criteria `{override_criteria_path}`."

        assert f"{lane}_EMPIRICAL_PACKET_05_STATUS_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_05_ARTIFACT_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_05_GATE_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_05_DECISION_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_05_EVIDENCE_TIER_v0" in doc_text
