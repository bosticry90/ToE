from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0.json"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_packet04_decision_policy_surface_is_pinned() -> None:
    protocol_text = _read(PROTOCOL_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    state_text = _read(STATE_PATH)

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_04_BASELINE_DECISION_v0") == (
        "INCONCLUSIVE_ONLY_UNTIL_PACKET05_OR_HIGHER"
    )

    for ref in (
        "formal/python/tests/test_foundational_empirical_packet04_decision_policy_gate.py",
        "formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0.json",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text


def test_packet04_framing_holds_next_step_inconclusive_policy() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and len(rows) == 7

    for lane, row in rows.items():
        assert "packet_04" in row["doc_path"].lower(), f"{lane}: doc_path drift"
        assert "packet_04" in row["artifact_path"].lower(), f"{lane}: artifact_path drift"
        assert "packet_04" in row["gate_path"].lower(), f"{lane}: gate_path drift"

        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact.get("payload", {})
        decision = payload.get("decision")
        assert decision in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}, (
            f"{lane}: unexpected packet-04 decision `{decision}`."
        )
        assert decision == "INCONCLUSIVE_v0", (
            f"{lane}: packet-04 baseline must remain INCONCLUSIVE_v0 until packet-05-or-higher policy transition."
        )
