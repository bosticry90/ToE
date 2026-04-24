from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARCHIVE_STATE_EXTRACT_PATH = REPO_ROOT / "archive" / "State_of_the_Theory_ARCHIVED_HISTORY_EXTRACT_v0.md"
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

PROOF_DEBT_CROSS_SURFACE_REFS = [
    "formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE01_v0.md",
    "formal/output/proof_debt_burndown_checkpoint_cycle01_v0.json",
    "formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE02_v0.md",
    "formal/output/proof_debt_burndown_checkpoint_cycle02_v0.json",
    "formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE03_v0.md",
    "formal/output/proof_debt_burndown_checkpoint_cycle03_v0.json",
    "formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE04_v0.md",
    "formal/output/proof_debt_burndown_checkpoint_cycle04_v0.json",
    "formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md",
    "formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json",
    "formal/output/toe_complete_v1_terminal_gate_checkpoint_v0.json",
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
    state_text = STATE_PATH.read_text(encoding="utf-8")
    inventory_text = INVENTORY_PATH.read_text(encoding="utf-8")
    archive_text = ARCHIVE_STATE_EXTRACT_PATH.read_text(encoding="utf-8")
    for gapid in TRACKED_GAPIDS:
        state_count = len(re.findall(rf"^GapID:\s*{re.escape(gapid)}\s*$", state_text, flags=re.MULTILINE))
        inventory_count = len(re.findall(rf"^GapID:\s*{re.escape(gapid)}\s*$", inventory_text, flags=re.MULTILINE))
        archive_count = len(re.findall(rf"^GapID:\s*{re.escape(gapid)}\s*$", archive_text, flags=re.MULTILINE))
        total_count = state_count + inventory_count + archive_count
        assert total_count == 1, (
            f"Expected exactly one canonical block for {gapid} across compact-State/inventory/archive, found {total_count}"
        )


def test_proof_debt_checkpoint_pointers_are_cross_surface_pinned() -> None:
    state_text = STATE_PATH.read_text(encoding="utf-8")
    roadmap_text = ROADMAP_PATH.read_text(encoding="utf-8")
    inventory_text = INVENTORY_PATH.read_text(encoding="utf-8")

    for ref in PROOF_DEBT_CROSS_SURFACE_REFS:
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
