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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
TERMINAL_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_complete_v1_terminal_gate_checkpoint_v0.json"
PROOF_DEBT_CHECKPOINT_PATHS = [
    REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle01_v0.json",
    REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle02_v0.json",
    REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle03_v0.json",
    REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle04_v0.json",
    REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle05_v0.json",
]
TRACKED_GAPIDS = [
    "COMP-FN-REP-GRID",
    "COMP-FN-REP-NONALIAS-EQUIV-01",
]


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_proof_debt_markers_use_stable_gapids() -> None:
    for path in PROOF_DEBT_CHECKPOINT_PATHS:
        payload = _load_json(path)
        markers = payload.get("target_markers")
        assert isinstance(markers, dict) and markers, f"Missing target_markers in {path}"

        marker_keys = set(markers)
        expected_keys = {f"gapid_{gapid}" for gapid in TRACKED_GAPIDS}
        assert marker_keys == expected_keys, (
            f"Unexpected marker keys in {path}. Expected {sorted(expected_keys)}, got {sorted(marker_keys)}"
        )
        assert not any(key.startswith("state_line_") for key in marker_keys), (
            f"Line-based marker key detected in {path}: {sorted(marker_keys)}"
        )


def test_terminal_checkpoint_tracks_gapids_not_lines() -> None:
    payload = _load_json(TERMINAL_CHECKPOINT_PATH)
    progress = payload.get("current_progress", {})

    refs = progress.get("critical_pending_marker_refs")
    assert isinstance(refs, list), "critical_pending_marker_refs must be a list"
    assert refs == [], "terminal gate closeout requires empty critical_pending_marker_refs"

    monitored = progress.get("critical_pending_gapids_monitored")
    assert monitored == TRACKED_GAPIDS, (
        "critical_pending_gapids_monitored must track the canonical proof-debt GapIDs"
    )

    assert payload.get("terminal_gate_result") == "SATISFIED_v0"


def test_tracked_gapids_exist_once_in_state_doc() -> None:
    text = STATE_PATH.read_text(encoding="utf-8")
    for gapid in TRACKED_GAPIDS:
        count = len(re.findall(rf"^GapID:\s*{re.escape(gapid)}\s*$", text, flags=re.MULTILINE))
        assert count == 1, f"Expected exactly one block for {gapid}, found {count}"
