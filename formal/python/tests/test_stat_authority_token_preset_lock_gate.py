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
STAT_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
TEMPLATE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"

FULL_TOKEN = "PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION"
INEV_TOKEN = "PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION"
PLACEHOLDER_VALUE = "ACTIVE_PREEXECUTION_v0_NONDISCHARGED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token_values(text: str, token_name: str) -> list[str]:
    return re.findall(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)


def test_stat_authority_token_preset_lock_gate() -> None:
    stat_plan_text = _read(STAT_PLAN_PATH)
    template_text = _read(TEMPLATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    matrix = _read_json(MATRIX_PATH)

    stat_locked = "| `PILLAR-STAT` | `LOCKED` |" in roadmap_text
    if stat_locked:
        assert "PILLAR-STAT" not in matrix.get("pillars", {}), (
            "STAT authority tokens must remain preset-only until `PILLAR-STAT` is explicitly registered in the matrix at activation."
        )
    else:
        assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
            "STAT authority token preset gate expects either the historical LOCKED posture or the canonical ACTIVE posture."
        )
        stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
        assert isinstance(stat_matrix, dict), "ACTIVE STAT posture must be present in the pillar status matrix."
        assert stat_matrix.get("matrix_status") == "ACTIVE", "PILLAR-STAT matrix status must be ACTIVE after activation."

    for token_name in (FULL_TOKEN, INEV_TOKEN):
        stat_values = _extract_token_values(stat_plan_text, token_name)
        assert stat_values == [PLACEHOLDER_VALUE], (
            f"{token_name} must be defined exactly once in STAT plan with `{PLACEHOLDER_VALUE}`."
        )

        assert token_name in template_text, f"Activation changeset template must pin token name `{token_name}`."
        assert _extract_token_values(template_text, token_name) == [], (
            f"Activation changeset template should pin token names, but not define `{token_name}` as a mirrored authority token line."
        )

        if stat_locked:
            assert token_name not in roadmap_text, (
                f"{token_name} must not be mirrored into roadmap while `PILLAR-STAT` is still LOCKED."
            )
            assert token_name not in state_text, (
                f"{token_name} must not be mirrored into State_of_the_Theory while `PILLAR-STAT` is still LOCKED."
            )
        else:
            assert _extract_token_values(roadmap_text, token_name) == [PLACEHOLDER_VALUE], (
                f"{token_name} must be mirrored into roadmap with the canonical placeholder value after activation."
            )
            assert _extract_token_values(state_text, token_name) == [PLACEHOLDER_VALUE], (
                f"{token_name} must be mirrored into State_of_the_Theory with the canonical placeholder value after activation."
            )

    assert f"`{PLACEHOLDER_VALUE}`" in template_text, "Activation template must pin the exact placeholder value."
    assert "STAT_AUTHORITY_TOKEN_PRESET_LOCK_v0: PINNED_NAMES_AND_PLACEHOLDER_VALUES_LOCKED_STAGE_ONLY" in stat_plan_text
    assert "do not mirror these token definitions into `PHYSICS_ROADMAP_v0.md`, `State_of_the_Theory.md`, or `PILLAR_STATUS_MATRIX_v1.json`" in stat_plan_text
    assert "Pinned token names:" in template_text
    assert "Pinned placeholder value (non-discharged; legacy-safe):" in template_text
