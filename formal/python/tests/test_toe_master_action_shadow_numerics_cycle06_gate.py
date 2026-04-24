from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE06_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_shadow_numerics_cycle06_v0.json"
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


def test_toe_master_action_shadow_numerics_cycle06_gate() -> None:
    text = _read(DOC_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert _extract_token(text, "TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE06_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(text, "TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE06_ARTIFACT_v0") == "toe_master_action_shadow_numerics_cycle06_v0"

    assert artifact.get("artifact_id") == "toe_master_action_shadow_numerics_cycle06_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    progression = payload.get("cycle_progression", {})
    assert progression.get("previous_cycle") == "toe_master_action_shadow_numerics_cycle05_v0"
    assert progression.get("current_cycle") == "toe_master_action_shadow_numerics_cycle06_v0"

    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE06_v0.md",
        "formal/python/tests/test_toe_master_action_shadow_numerics_cycle06_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
