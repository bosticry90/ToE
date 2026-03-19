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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_packet02_matrix_surface_is_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert matrix.get("matrix_id") == "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0"
    assert matrix.get("matrix_version") == 1
    assert matrix.get("protocol_doc") == "formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
    assert set(matrix.get("allowed_decisions", [])) == {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}

    for ref in (
        "formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json",
        "formal/python/tests/test_foundational_empirical_packet02_matrix_consistency_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text


def test_packet02_rows_match_docs_and_artifacts() -> None:
    matrix = _read_json(MATRIX_PATH)
    protocol_text = _read(PROTOCOL_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and len(rows) == 7

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0") == (
        "RETAIN_OR_PRUNE_ALLOWED_WITH_PROTOCOL_GUARDS"
    )

    for lane, row in sorted(rows.items()):
        doc_path = REPO_ROOT / row["doc_path"]
        artifact_path = REPO_ROOT / row["artifact_path"]
        gate_path = REPO_ROOT / row["gate_path"]

        doc_text = _read(doc_path)
        artifact = _read_json(artifact_path)
        payload = artifact.get("payload", {})

        assert gate_path.exists(), f"{lane}: missing gate path `{gate_path}`."
        assert artifact.get("artifact_id", "").endswith("_packet_02_v0")
        assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
        assert payload.get("decision") in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}
        assert payload.get("evidence_tier") in {"INTERMEDIATE_v0", "DISCHARGE_GRADE_v0"}

        eligibility = payload.get("decision_eligibility")
        assert isinstance(eligibility, dict)
        assert eligibility.get("retain_allowed") is True
        assert eligibility.get("prune_allowed") is True
        assert eligibility.get("prune_guard_satisfied") is True

        if payload.get("decision") == "PRUNE_v0":
            uncertainty = str(payload.get("uncertainty_annotation", "")).lower()
            assert "scaffold" not in uncertainty

        if payload.get("decision") != "INCONCLUSIVE_v0":
            decision_record_pointer = payload.get("decision_record_pointer")
            assert isinstance(decision_record_pointer, str) and decision_record_pointer, (
                f"{lane}: non-inconclusive packet-02 decision requires decision_record_pointer."
            )
            assert (REPO_ROOT / decision_record_pointer).exists(), (
                f"{lane}: decision_record_pointer file missing `{decision_record_pointer}`."
            )

        assert f"{lane}_EMPIRICAL_PACKET_02_STATUS_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_02_ARTIFACT_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_02_GATE_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_02_DECISION_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_02_EVIDENCE_TIER_v0" in doc_text
        assert f"{lane}_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0" in doc_text

        for ref in (row["doc_path"], row["gate_path"]):
            assert ref in roadmap_text
            assert ref in state_text or ref in inventory_text
