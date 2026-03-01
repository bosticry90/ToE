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
COSMO_MICRO07_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_07_MATRIX_LANE_DRIFT_ALARM_v0.md"
)
COSMO_MICRO07_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_bg_micro07_matrix_lane_drift_alarm_cycle01_v0.json"
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


def test_cosmo_micro07_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO07_PATH.exists(), "Missing COSMO background Cycle-007 micro document."
    assert COSMO_MICRO07_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-007 artifact payload."


def test_cosmo_target_references_micro07_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-MICRO-07-MATRIX-LANE-DRIFT-ALARM-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_07_MATRIX_LANE_DRIFT_ALARM_v0.md",
        "formal/output/cosmo_bg_micro07_matrix_lane_drift_alarm_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-07 token(s): " + ", ".join(missing)


def test_cosmo_micro07_doc_contains_required_tokens() -> None:
    text = _read(COSMO_MICRO07_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_07_MATRIX_LANE_DRIFT_ALARM_v0",
        "TARGET-COSMO-BG-MICRO-07-MATRIX-LANE-DRIFT-ALARM-v0",
        "COSMO_BG_MICRO07_MATRIX_LANE_DRIFT_ALARM_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO07_SCOPE_BOUNDARY_v0: MATRIX_LANE_DRIFT_ALARM_ONLY_NONCLAIM",
        "COSMO_BG_MICRO07_PROGRESS_v0: MATRIX_LANE_DRIFT_ALARM_TOKEN_PINNED",
        "COSMO_BG_MICRO07_MATRIX_LANE_DRIFT_ALARM_ARTIFACT_v0: cosmo_bg_micro07_matrix_lane_drift_alarm_cycle01_v0",
        "COSMO_MATRIX_LANE_DRIFT_ALARM_POLICY_v0: LOCKED_QUEUE_ENFORCED_CROSS_SURFACE",
        "lane_transition_policy: LOCKED_QUEUE_ENFORCED_CROSS_SURFACE",
        "lane_drift_alarm_gate: formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO micro-07 document is missing required token(s): " + ", ".join(missing)


def test_cosmo_matrix_roadmap_registry_state_are_locked_queue_aligned() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
    assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."

    assert cosmo.get("matrix_status") == "LOCKED"
    assert cosmo.get("target_id") == "TARGET-COSMO-BG-PLAN"
    assert cosmo.get("prereq_targets") == "TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN"
    assert cosmo.get("lane_transition_policy") == "LOCKED_QUEUE_ENFORCED_CROSS_SURFACE"
    assert cosmo.get("lane_drift_alarm_gate") == "formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py"

    status, target_id, target_path, prereqs = _cosmo_roadmap_row(_read(ROADMAP_PATH))
    assert status == "LOCKED"
    assert status == cosmo.get("matrix_status")
    assert target_id == cosmo.get("target_id")
    assert target_path == cosmo.get("target_doc")
    assert prereqs == cosmo.get("prereq_targets")

    registry = _read_json(REGISTRY_PATH)
    pillars = registry.get("pillars", [])
    cosmo_rows = [row for row in pillars if row.get("pillar_id") == "PILLAR-COSMO"]
    assert len(cosmo_rows) == 1, "Registry must contain exactly one PILLAR-COSMO row."
    cosmo_registry = cosmo_rows[0]
    assert cosmo_registry.get("mode") == "LOCKED_QUEUE"
    assert cosmo_registry.get("roadmap_status") == "LOCKED"
    assert cosmo_registry.get("target_id") == "TARGET-COSMO-BG-PLAN"

    state_text = _read(STATE_PATH)
    state_required = [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-COSMO",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
        "COSMO_MATRIX_LANE_DRIFT_ALARM_POLICY_v0: LOCKED_QUEUE_ENFORCED_CROSS_SURFACE",
        "formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py",
    ]
    missing = [token for token in state_required if token not in state_text]
    assert not missing, "State missing COSMO lane drift-alarm token(s): " + ", ".join(missing)


def test_cosmo_micro07_artifact_schema_and_token_alignment() -> None:
    payload = _read_json(COSMO_MICRO07_ARTIFACT_PATH)

    assert payload.get("artifact_id") == "cosmo_bg_micro07_matrix_lane_drift_alarm_cycle01_v0"
    assert payload.get("artifact_version") == "v0"
    assert payload.get("placeholder_template") is True

    body = payload.get("payload")
    assert isinstance(body, dict), "Artifact payload block must be an object."
    assert body.get("checkpoint") == "cosmo_bg_micro07_matrix_lane_drift_alarm_cycle01"
    assert body.get("status") == "placeholder_non_promotional"
    assert body.get("scope") == "matrix_lane_drift_alarm_only_nonclaim_v0"

    policy_tokens = body.get("policy_tokens")
    assert isinstance(policy_tokens, list) and len(policy_tokens) == 3
    for token in [
        "COSMO_MATRIX_LANE_DRIFT_ALARM_POLICY_v0: LOCKED_QUEUE_ENFORCED_CROSS_SURFACE",
        "lane_transition_policy: LOCKED_QUEUE_ENFORCED_CROSS_SURFACE",
        "lane_drift_alarm_gate: formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py",
    ]:
        assert token in policy_tokens

    required_surfaces = body.get("required_locked_queue_surfaces")
    assert isinstance(required_surfaces, list) and len(required_surfaces) == 4

    required_tokens = body.get("required_locked_queue_tokens")
    assert isinstance(required_tokens, list) and len(required_tokens) == 5
