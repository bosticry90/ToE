from __future__ import annotations

import json
from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def load_surface_texts() -> tuple[str, str, str]:
    state = _read(Path("State_of_the_Theory.md"))
    inventory = _read(Path("formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))
    return state, inventory, roadmap


def assert_discharge_tokens(
    discharge_text: str,
    progress_token: str,
    gate_token: str,
    scope_token: str,
    artifact_rel: str,
) -> None:
    assert progress_token in discharge_text
    assert gate_token in discharge_text
    assert scope_token in discharge_text
    assert artifact_rel in discharge_text
    assert Path(artifact_rel).stem in discharge_text


def assert_state_inventory_roadmap_tokens(
    state_text: str,
    inventory_text: str,
    roadmap_text: str,
    required_tokens: list[str],
) -> None:
    for token in required_tokens:
        assert token in state_text or token in inventory_text
        assert token in roadmap_text


def assert_artifact_contract(
    artifact_rel: str,
    expected_id: str,
    cycle: int,
    expected_status_key: str,
    expected_status_value: str,
    source_cycles: list[int] | None = None,
    extra_expected_lines: tuple[str, ...] = (),
) -> None:
    artifact_text = _read(Path(artifact_rel))

    assert f'"artifact_id": "{expected_id}"' in artifact_text
    assert f'"cycle": {cycle}' in artifact_text
    assert f'"{expected_status_key}": "{expected_status_value}"' in artifact_text
    assert '"token_write_allowed": false' in artifact_text

    if source_cycles is not None:
        assert f'"source_cycles": {json.dumps(source_cycles)}' in artifact_text

    for expected_line in extra_expected_lines:
        assert expected_line in artifact_text