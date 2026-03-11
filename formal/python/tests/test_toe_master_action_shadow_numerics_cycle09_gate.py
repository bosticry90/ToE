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
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE09_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_shadow_numerics_cycle09_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_toe_master_action_shadow_numerics_cycle09_gate() -> None:
    text = _read(DOC_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert _extract_token(text, "TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE09_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(text, "TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE09_ARTIFACT_v0") == "toe_master_action_shadow_numerics_cycle09_v0"

    assert artifact.get("artifact_id") == "toe_master_action_shadow_numerics_cycle09_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    progression = payload.get("cycle_progression", {})
    assert progression.get("previous_cycle") == "toe_master_action_shadow_numerics_cycle08_v0"
    assert progression.get("current_cycle") == "toe_master_action_shadow_numerics_cycle09_v0"
