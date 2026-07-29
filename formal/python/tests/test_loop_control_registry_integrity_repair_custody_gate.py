from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.historical_artifact_currency_identity import verify_binding
from formal.python.tools.loop_control_registry_integrity import (
    DEFAULT_REGISTRY_PATH,
    casefold_collisions,
)


REPO_ROOT = find_repo_root(Path(__file__))
RECORD_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "LOOP_CONTROL_REGISTRY_INTEGRITY_REPAIR_20260711_v0.json"
)


def _record() -> dict:
    return json.loads(RECORD_PATH.read_text(encoding="utf-8"))


def test_registry_repair_custody_binds_pre_and_post_bytes() -> None:
    record = _record()
    before = record["pre_repair"]
    after = record["post_repair"]

    historical = subprocess.run(
        ["git", "show", f"{before['repository_commit']}:{before['path']}"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    post_repair = verify_binding(
        "PAC-001",
        expected_path=after["path"],
        expected_sha256=after["sha256"],
    )

    assert len(historical) == before["size_bytes"]
    assert hashlib.sha256(historical).hexdigest() == before["sha256"]
    assert post_repair["bytes"] == after["size_bytes"]
    assert post_repair["sha256"] == after["sha256"]
    assert post_repair["role"] == "HISTORICAL_SOURCE_BLOB"
    assert post_repair["current_successor_role"] == "CURRENT_CANONICAL_IDENTITY"

    historical_payload = json.loads(historical)
    stale_projection = historical_payload["active_workstreams"][0]
    stale_bytes = json.dumps(
        stale_projection, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    expected_stale = before["stale_active_workstream_projection"]
    assert len(stale_projection) == expected_stale["key_count"]
    assert len(stale_bytes) == expected_stale["canonical_json_size_bytes"]
    assert hashlib.sha256(stale_bytes).hexdigest() == expected_stale["row_sha256"]

    historical_state = historical_payload["current_target_state"]
    state_bytes = json.dumps(
        historical_state, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    expected_state = before["flattened_current_target_state"]
    assert len(historical_state) == expected_state["key_count"]
    assert len(state_bytes) == expected_state["canonical_json_size_bytes"]
    assert hashlib.sha256(state_bytes).hexdigest() == expected_state["row_sha256"]

    assert historical_payload["CURRENT_LIVE_NEXT_TARGET_v0"] == (
        historical_state["live_next_target"]
    )
    assert historical_payload["ACTIVE_LANE_v0"] == historical_state["live_next_target"]


def test_registry_repair_preserves_current_target_and_nonclaim_boundary() -> None:
    record = _record()
    after = record["post_repair"]
    frozen = verify_binding(
        "PAC-001",
        expected_path=after["path"],
        expected_sha256=after["sha256"],
    )
    frozen_bytes = subprocess.run(
        [
            "git",
            "show",
            f"{frozen['frozen_commit']}:{frozen['path']}",
        ],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    registry = json.loads(frozen_bytes)

    assert after["current_target"] == registry["current_target_state"]["live_next_target"]
    assert after["current_target"] == "execute_pillar_seam_unit_mapping_ledger_v0"
    assert after["schema_id"] == registry["schema_id"]
    assert after["status"] == registry["status"]
    assert after["deprecated_casefold_alias_rows"] == len(
        registry["casefold_key_aliases_v0"]
    )
    assert after["documented_duplicate_workstream_id_count"] == registry[
        "duplicate_workstream_id_quarantine_v0"
    ]["collision_count"]
    state_contract = registry["current_target_state_authority_contract_v0"]
    assert after["flattened_current_state_compatibility_key_count"] == state_contract[
        "flattened_compatibility_key_count"
    ]
    assert after["flattened_current_state_compatibility_sha256"] == state_contract[
        "flattened_compatibility_sha256"
    ]
    assert casefold_collisions(registry) == []
    assert record["boundary"] == {
        "embedded_stale_active_projection_removed": True,
        "git_history_preserved": True,
        "historical_workstream_catalog_preserved": True,
        "live_target_changed": False,
        "scientific_artifacts_modified": False,
        "scientific_claim_changed": False,
    }
