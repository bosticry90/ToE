from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
COSMO_MICRO08_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_08_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_v0.md"
)
COSMO_MICRO08_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_bg_micro08_locked_queue_unlock_transition_packet_cycle01_v0.json"
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


def _extract_target_id(text: str) -> str:
    match = re.search(r"\bTARGET-COSMO-BG-MICRO-08-[A-Z0-9-]+-v0\b", text)
    assert match is not None, "Missing Cycle-008 TARGET token in COSMO micro document."
    return match.group(0)


def _extract_assignment_value(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([^\n\r]+)", text)
    assert match is not None, f"Missing `{token_name}` assignment in COSMO micro-08 document."
    return match.group(1).strip().strip("`")


def _cosmo_roadmap_row(roadmap_text: str) -> tuple[str, str, str, str]:
    active_text, _ = split_active_and_archived(roadmap_text, ROADMAP_PATH)
    match = re.search(
        r"^\|\s*`PILLAR-COSMO`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|",
        active_text,
        flags=re.MULTILINE,
    )
    assert match is not None, "Missing active roadmap row for PILLAR-COSMO."
    return match.groups()


def test_cosmo_micro08_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO08_PATH.exists(), "Missing COSMO background Cycle-008 micro document."
    assert COSMO_MICRO08_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-008 artifact payload."


def test_cosmo_target_references_micro08_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    micro_text = _read(COSMO_MICRO08_PATH)
    micro_target_id = _extract_target_id(micro_text)
    required_tokens = [
        micro_target_id,
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_08_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_v0.md",
        "formal/output/cosmo_bg_micro08_locked_queue_unlock_transition_packet_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-08 token(s): " + ", ".join(missing)


def test_cosmo_micro08_doc_contains_required_tokens() -> None:
    text = _read(COSMO_MICRO08_PATH)
    micro_target_id = _extract_target_id(text)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_08_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_v0",
        micro_target_id,
        "COSMO_BG_MICRO08_UNLOCK_TRANSITION_PACKET_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO08_SCOPE_BOUNDARY_v0: LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_ONLY_NONCLAIM",
        "COSMO_BG_MICRO08_PROGRESS_v0: UNLOCK_TRANSITION_PACKET_TOKEN_PINNED",
        "COSMO_BG_MICRO08_UNLOCK_TRANSITION_PACKET_ARTIFACT_v0: cosmo_bg_micro08_locked_queue_unlock_transition_packet_cycle01_v0",
        "COSMO_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_POLICY_v0: PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP",
        "unlock_transition_packet_policy: PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP",
        "unlock_transition_packet_gate: formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO micro-08 document is missing required token(s): " + ", ".join(missing)


def test_cosmo_unlock_transition_packet_keeps_locked_queue_status() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
    assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."

    assert cosmo.get("matrix_status") == "CLOSED"
    assert cosmo.get("unlock_transition_packet_doc") == (
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_08_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_v0.md"
    )
    assert cosmo.get("unlock_transition_packet_gate") == (
        "formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py"
    )
    assert cosmo.get("unlock_transition_packet_policy") == "PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP"

    status, target_id, target_path, prereqs = _cosmo_roadmap_row(_read(ROADMAP_PATH))
    assert status == "CLOSED"
    assert target_id == "TARGET-COSMO-BG-PLAN"
    assert target_path == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
    assert prereqs == "TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN"

    registry = _read_json(REGISTRY_PATH)
    rows = [row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-COSMO"]
    assert len(rows) == 1
    assert rows[0].get("mode") == "CLOSED_HANDOFF"
    assert rows[0].get("expected_matrix_status") == "CLOSED"

    state_text = _read(STATE_PATH)
    required_state_tokens = [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-COSMO",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
        "COSMO_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_POLICY_v0: PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP",
        "formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py",
    ]
    missing = [token for token in required_state_tokens if token not in state_text]
    assert not missing, "State missing COSMO unlock transition packet token(s): " + ", ".join(missing)


def test_cosmo_micro08_artifact_schema_and_token_alignment() -> None:
    micro_text = _read(COSMO_MICRO08_PATH)
    artifact_id = _extract_assignment_value(micro_text, "COSMO_BG_MICRO08_UNLOCK_TRANSITION_PACKET_ARTIFACT_v0")
    checkpoint = artifact_id.removesuffix("_v0")

    payload = _read_json(COSMO_MICRO08_ARTIFACT_PATH)

    assert payload.get("artifact_id") == artifact_id
    assert payload.get("artifact_version") == "v0"
    assert payload.get("placeholder_template") is True

    body = payload.get("payload")
    assert isinstance(body, dict)
    assert body.get("checkpoint") == checkpoint
    assert body.get("status") == "placeholder_non_promotional"
    assert body.get("scope") == "locked_queue_unlock_transition_packet_only_nonclaim_v0"

    policy_tokens = body.get("policy_tokens")
    assert isinstance(policy_tokens, list) and len(policy_tokens) == 3

    conditions = body.get("required_preauthorized_unlock_conditions")
    assert isinstance(conditions, list) and len(conditions) == 5


