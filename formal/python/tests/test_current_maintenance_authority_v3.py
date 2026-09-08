from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
AUTHORITY_PATH = ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v3.json"
V4_AUTHORITY_PATH = ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v4.json"


def _read(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_v3_authorizes_only_canonical_text_attribute_repair() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == "ACTIVE_CANONICAL_TEXT_ATTRIBUTE_REPAIR_ONLY"
    assert authority["current_maintenance_target"] == (
        "execute_canonical_text_attribute_policy_repair_v0"
    )
    scope = authority["authorized_scope"]
    assert isinstance(scope, dict)
    assert scope["repository_wide_renormalization_authorized"] is False
    boundary = authority["boundary"]
    assert isinstance(boundary, dict)
    assert boundary["historical_bytes_may_be_rewritten"] is False
    assert boundary["scientific_target_rotated"] is False


def test_v4_preserves_v3_as_immutable_execution_history() -> None:
    authority_bytes = AUTHORITY_PATH.read_bytes()
    successor = _read(V4_AUTHORITY_PATH)
    previous = successor["previous_maintenance_authority"]
    assert isinstance(previous, dict)
    assert previous["path"] == (
        "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v3.json"
    )
    assert previous["sha256"] == hashlib.sha256(
        authority_bytes
    ).hexdigest()
