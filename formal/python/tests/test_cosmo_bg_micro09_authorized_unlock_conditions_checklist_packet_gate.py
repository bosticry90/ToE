from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
COSMO_MICRO09_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_09_AUTHORIZED_UNLOCK_CONDITIONS_CHECKLIST_PACKET_v0.md"
)
COSMO_MICRO09_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_cycle01_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _cosmo_roadmap_row(roadmap_text: str) -> tuple[str, str, str, str]:
    active_text, _ = split_active_and_archived(roadmap_text, ROADMAP_PATH)
    match = re.search(
        r"^\|\s*`PILLAR-COSMO`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|",
        active_text,
        flags=re.MULTILINE,
    )
    assert match is not None, "Missing active roadmap row for PILLAR-COSMO."
    return match.groups()


def test_cosmo_micro09_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO09_PATH.exists(), "Missing COSMO background Cycle-009 micro document."
    assert COSMO_MICRO09_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-009 artifact payload."


def test_cosmo_target_references_micro09_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-MICRO-09-AUTHORIZED-UNLOCK-CONDITIONS-CHECKLIST-PACKET-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_09_AUTHORIZED_UNLOCK_CONDITIONS_CHECKLIST_PACKET_v0.md",
        "formal/output/cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-09 token(s): " + ", ".join(missing)


def test_cosmo_micro09_doc_contains_required_tokens() -> None:
    text = _read(COSMO_MICRO09_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_09_AUTHORIZED_UNLOCK_CONDITIONS_CHECKLIST_PACKET_v0",
        "TARGET-COSMO-BG-MICRO-09-AUTHORIZED-UNLOCK-CONDITIONS-CHECKLIST-PACKET-v0",
        "COSMO_BG_MICRO09_AUTHORIZED_UNLOCK_CHECKLIST_PACKET_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO09_SCOPE_BOUNDARY_v0: AUTHORIZED_UNLOCK_CHECKLIST_PACKET_ONLY_NONCLAIM",
        "COSMO_BG_MICRO09_PROGRESS_v0: AUTHORIZED_UNLOCK_CHECKLIST_PACKET_TOKEN_PINNED",
        "COSMO_BG_MICRO09_AUTHORIZED_UNLOCK_CHECKLIST_PACKET_ARTIFACT_v0: cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_cycle01_v0",
        "COSMO_AUTHORIZED_UNLOCK_CHECKLIST_PACKET_POLICY_v0: CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE",
        "authorized_unlock_checklist_policy: CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE",
        "authorized_unlock_checklist_gate: formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO micro-09 document is missing required token(s): " + ", ".join(missing)


def test_cosmo_authorized_unlock_checklist_packet_keeps_locked_queue_status() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
    assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."

    assert cosmo.get("matrix_status") == "LOCKED"
    assert cosmo.get("authorized_unlock_checklist_doc") == (
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_09_AUTHORIZED_UNLOCK_CONDITIONS_CHECKLIST_PACKET_v0.md"
    )
    assert cosmo.get("authorized_unlock_checklist_gate") == (
        "formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py"
    )
    assert cosmo.get("authorized_unlock_checklist_policy") == "CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE"

    status, target_id, target_path, prereqs = _cosmo_roadmap_row(_read(ROADMAP_PATH))
    assert status == "LOCKED"
    assert target_id == "TARGET-COSMO-BG-PLAN"
    assert target_path == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
    assert prereqs == "TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN"

    registry = _read_json(REGISTRY_PATH)
    rows = [row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-COSMO"]
    assert len(rows) == 1
    assert rows[0].get("mode") == "LOCKED_QUEUE"
    assert rows[0].get("roadmap_status") == "LOCKED"

    state_text = _read(STATE_PATH)
    required_state_tokens = [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-COSMO",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
        "COSMO_AUTHORIZED_UNLOCK_CHECKLIST_PACKET_POLICY_v0: CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE",
        "formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py",
    ]
    missing = [token for token in required_state_tokens if token not in state_text]
    assert not missing, "State missing COSMO authorized unlock checklist packet token(s): " + ", ".join(missing)


def test_cosmo_micro09_artifact_schema_and_token_alignment() -> None:
    payload = _read_json(COSMO_MICRO09_ARTIFACT_PATH)

    assert payload.get("artifact_id") == "cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_cycle01_v0"
    assert payload.get("artifact_version") == "v0"
    assert payload.get("placeholder_template") is True

    body = payload.get("payload")
    assert isinstance(body, dict)
    assert body.get("checkpoint") == "cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_cycle01"
    assert body.get("status") == "placeholder_non_promotional"
    assert body.get("scope") == "authorized_unlock_checklist_packet_only_nonclaim_v0"

    policy_tokens = body.get("policy_tokens")
    assert isinstance(policy_tokens, list) and len(policy_tokens) == 3

    checklist_items = body.get("authorized_unlock_checklist_items")
    assert isinstance(checklist_items, list) and len(checklist_items) == 5
