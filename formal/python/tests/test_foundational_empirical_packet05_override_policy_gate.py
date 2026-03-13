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
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_PACKET05_OVERRIDE_POLICY_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet05_override_policy_is_pinned() -> None:
    policy_text = _read(POLICY_PATH)
    matrix = _read_json(MATRIX_PATH)

    for token in (
        "FOUNDATIONAL_EMPIRICAL_PACKET05_OVERRIDE_POLICY_v0",
        "FOUNDATIONAL_EMPIRICAL_PACKET_05_OVERRIDE_MODE_v0: GR_SR_ACTIVE_OVERRIDE_CRITERIA_PINNED",
        "FOUNDATIONAL_EMPIRICAL_PACKET_05_OVERRIDE_ALLOWED_DECISIONS_v0: RETAIN_OR_PRUNE_WITH_EXPLICIT_CRITERIA",
    ):
        assert token in policy_text

    assert matrix.get("override_policy_doc") == "formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_OVERRIDE_POLICY_v0.md"

    for text in (_read(STATE_PATH), _read(ROADMAP_PATH)):
        assert "formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_OVERRIDE_POLICY_v0.md" in text
        assert "formal/python/tests/test_foundational_empirical_packet05_override_policy_gate.py" in text


def test_packet05_override_rows_have_criteria_docs_for_noninconclusive_decisions() -> None:
    matrix = _read_json(MATRIX_PATH)
    for lane, row in matrix["rows"].items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        if artifact["payload"]["decision"] != "INCONCLUSIVE_v0":
            assert (REPO_ROOT / row["override_criteria_path"]).exists(), f"{lane}: missing override criteria doc."