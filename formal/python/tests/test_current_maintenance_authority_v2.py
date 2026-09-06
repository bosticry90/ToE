from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


ROOT = find_repo_root(Path(__file__))
AUTHORITY_PATH = ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v2.json"
POINTER_PATH = ROOT / (
    "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json"
)
V1_PATH = ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v1.json"
REGISTRY_PATH = ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
AUTHORITY_SHA256 = (
    "05a74c18a5a13d6661e6de13fa14951837a8ca9ac40a9ca107f8a1de8d10e9aa"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_v2_is_hash_exact_and_pointer_resolves_it() -> None:
    authority = _read(AUTHORITY_PATH)
    pointer = _read(POINTER_PATH)
    assert _sha256(AUTHORITY_PATH) == AUTHORITY_SHA256
    assert pointer["current_authority_path"] == (
        "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v2.json"
    )
    assert pointer["current_authority_schema_id"] == "CURRENT_MAINTENANCE_AUTHORITY_v2"
    assert pointer["current_authority_sha256"] == AUTHORITY_SHA256
    assert authority["status"] == "COMPLETE_ACCEPTED_NO_AUTOMATIC_SUCCESSOR"


def test_v2_preserves_v1_result_review_and_handoff_custody() -> None:
    authority = _read(AUTHORITY_PATH)
    assert _sha256(V1_PATH) == authority["previous_maintenance_authority"]["sha256"]
    for key in ("completion_result_review", "post_maintenance_handoff"):
        record = authority[key]
        assert _sha256(ROOT / record["path"]) == record["sha256"]


def test_v2_preserves_closeout_scientific_snapshot_without_overriding_live_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    pointer = _read(POINTER_PATH)
    registry = _read(REGISTRY_PATH)
    closeout_target = authority["scientific_authority"]["current_target"]
    live_target = registry["current_projection_v0"]["current_target"]
    assert closeout_target == (
        "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
        "route_selection_packet_v2"
    )
    assert pointer["scientific_target"] == closeout_target
    assert live_target != closeout_target
    assert authority["scientific_authority"]["target_rotated"] is False
    assert authority["post_maintenance_handoff"]["selected_route"] is None
    assert authority["successor"]["automatic_maintenance_successor"] is None
    assert authority["successor"]["automatic_scientific_successor"] is None


def test_v2_closes_maintenance_and_keeps_prohibited_effects_false() -> None:
    authority = _read(AUTHORITY_PATH)
    boundary = authority["boundary"]
    assert boundary["maintenance_execution_complete"] is True
    assert boundary["maintenance_result_review_accepted"] is True
    for field, value in boundary.items():
        if field in ("maintenance_execution_complete", "maintenance_result_review_accepted"):
            continue
        assert value is False
