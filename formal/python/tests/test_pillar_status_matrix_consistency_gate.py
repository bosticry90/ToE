from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _roadmap_status_for_pillar(active_text: str, pillar_id: str) -> str:
    match = re.search(
        rf"^\|\s*`{re.escape(pillar_id)}`\s*\|\s*`([^`]+)`\s*\|",
        active_text,
        flags=re.MULTILINE,
    )
    assert match is not None, f"Missing active roadmap row for {pillar_id}."
    return match.group(1)


def test_pillar_status_matrix_rows_match_discharge_docs_and_roadmap() -> None:
    matrix = _read_json(MATRIX_PATH)
    pillars = matrix.get("pillars", {})
    assert isinstance(pillars, dict) and pillars, "Matrix must define at least one pillar row."

    roadmap_active, _ = split_active_and_archived(_read(ROADMAP_PATH), ROADMAP_PATH)
    for pillar_id, row in pillars.items():
        assert isinstance(row, dict), f"Matrix row for {pillar_id} must be an object."
        required_fields = [
            "discharge_doc",
            "full_derivation_token",
            "inevitability_token",
            "full_derivation",
            "inevitability",
            "matrix_status",
        ]
        missing = [field for field in required_fields if field not in row]
        assert not missing, f"Matrix row {pillar_id} missing required field(s): {', '.join(missing)}"

        discharge_path = REPO_ROOT / row["discharge_doc"]
        discharge_text = _read(discharge_path)

        full_derivation_value = _extract_token(discharge_text, row["full_derivation_token"])
        inevitability_value = _extract_token(discharge_text, row["inevitability_token"])
        assert row["full_derivation"] == full_derivation_value, (
            f"{pillar_id} full_derivation drift between matrix and discharge doc."
        )
        assert row["inevitability"] == inevitability_value, (
            f"{pillar_id} inevitability drift between matrix and discharge doc."
        )

        roadmap_status = _roadmap_status_for_pillar(roadmap_active, pillar_id)
        if pillar_id == "PILLAR-STAT" and roadmap_status == "ACTIVE":
            assert row["matrix_status"] in {"ACTIVE", "CLOSED"}, (
                "PILLAR-STAT staged handoff may present ACTIVE roadmap posture with CLOSED matrix status."
            )
        else:
            assert row["matrix_status"] == roadmap_status, (
                f"{pillar_id} matrix_status drift between matrix and roadmap."
            )


def test_pillar_status_matrix_qft_entry_matches_state_tokens() -> None:
    matrix = _read_json(MATRIX_PATH)
    qft_entry = matrix.get("pillars", {}).get("PILLAR-QFT", {})
    assert qft_entry, "Matrix must define PILLAR-QFT entry."

    state_text = _read(STATE_PATH)
    state_adjudication = _extract_token(state_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    state_inevitability = _extract_token(state_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")
    assert qft_entry.get("full_derivation") == state_adjudication
    assert qft_entry.get("inevitability") == state_inevitability
