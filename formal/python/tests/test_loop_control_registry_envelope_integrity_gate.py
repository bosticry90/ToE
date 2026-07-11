from __future__ import annotations

import json

import pytest

from formal.python.tools.loop_control_registry_integrity import (
    CANONICAL_CASEFOLD_KEYS,
    CURRENT_PROJECTION_SCHEMA_ID,
    CURRENT_STATE_AUTHORITY_CONTRACT_SCHEMA_ID,
    CURRENT_STATE_AUTHORITY_KEYS,
    REGISTRY_SCHEMA_ID,
    REGISTRY_STATUS,
    RegistryIntegrityError,
    atomic_write_registry,
    casefold_collisions,
    load_registry,
    repair_registry,
    validate_registry,
)


def test_unequal_casefold_aliases_fail_closed() -> None:
    with pytest.raises(ValueError, match="case-fold collision with unequal values"):
        repair_registry(
            {
                "CURRENT_LIVE_NEXT_TARGET_v0": "target_v0",
                "ACTIVE_LANE_v0": "target_v0",
                "current_target_state": {
                    "schema_id": "CURRENT_TARGET_STATE_v0",
                    "live_next_target": "target_v0",
                    "previous_live_next_target": "previous_v0",
                    "live_next_target_kind": "execution",
                    "live_next_target_evidence": "evidence.json",
                    "live_next_target_report": "report.json",
                    "live_next_target_outcome": "PENDING",
                    "live_next_target_strict_outcome": "PENDING_NONCLAIM",
                },
                "workstreams": [
                    {
                        "workstream_id": "target_v0",
                        "status": "active",
                        "Example": {"value": 1},
                        "example": {"value": 2},
                    }
                ],
            }
        )


def test_pre_repair_authority_disagreement_fails_closed() -> None:
    with pytest.raises(ValueError, match="pre-repair authority disagreement"):
        repair_registry(
            {
                "CURRENT_LIVE_NEXT_TARGET_v0": "different_v0",
                "ACTIVE_LANE_v0": "target_v0",
                "current_target_state": {
                    "schema_id": "CURRENT_TARGET_STATE_v0",
                    "live_next_target": "target_v0",
                },
            }
        )


def test_casefold_canonical_spellings_are_explicit() -> None:
    assert CANONICAL_CASEFOLD_KEYS == {
        "a_source_ck_rule_candidate": "A_source_ck_rule_candidate",
        "bianchi_compatibility_claimed": "Bianchi_compatibility_claimed",
        "ccft_validated": "ccft_validated",
        "full_maxwell_closure_claimed": "full_maxwell_closure_claimed",
        "full_scalar_qft_closure_claimed": "full_scalar_qft_closure_claimed",
        "selected_a_ck_constraint_family": "selected_A_ck_constraint_family",
    }


def test_atomic_registry_writer_validates_before_replace(tmp_path) -> None:
    path = tmp_path / "registry.json"
    original = b'{"status":"original"}\n'
    replacement = b'{"schema_id":"replacement"}\n'
    path.write_bytes(original)

    atomic_write_registry(path, replacement)
    assert path.read_bytes() == replacement

    with pytest.raises((json.JSONDecodeError, RegistryIntegrityError)):
        atomic_write_registry(path, b'{"truncated":')
    assert path.read_bytes() == replacement


def test_registry_envelope_and_current_projection_are_canonical() -> None:
    registry = load_registry()
    state = registry["current_target_state"]
    target = state["live_next_target"]

    assert registry["schema_id"] == REGISTRY_SCHEMA_ID
    assert registry["status"] == REGISTRY_STATUS
    assert registry["ACTIVE_LANE_v0"] == target
    assert registry["CURRENT_LIVE_NEXT_TARGET_v0"] == target
    assert registry["active_lane"] == target
    assert registry["active_lanes"] == [target]
    assert registry["active_workstream"] == target
    assert registry["active_workstream_count"] == 1
    assert [row["workstream_id"] for row in registry["active_workstreams"]] == [target]

    projection = registry["current_projection_v0"]
    assert projection["schema_id"] == CURRENT_PROJECTION_SCHEMA_ID
    assert projection["current_target"] == target
    assert projection["previous_target"] == state["previous_live_next_target"]
    assert projection["current_target_evidence"] == state["live_next_target_evidence"]
    assert projection["current_target_report"] == state["live_next_target_report"]

    alias_values = {
        "live_next_target": target,
        "current_live_next_target": target,
        "current_live_target": target,
        "current_target": target,
        "active_lane": target,
        "active_workstream": target,
        "live_next_target_kind": state["live_next_target_kind"],
        "current_live_target_kind": state["live_next_target_kind"],
        "current_target_kind": state["live_next_target_kind"],
        "live_next_target_evidence": state["live_next_target_evidence"],
        "current_live_target_evidence": state["live_next_target_evidence"],
        "current_target_evidence": state["live_next_target_evidence"],
        "live_next_target_report": state["live_next_target_report"],
        "current_live_target_report": state["live_next_target_report"],
        "current_target_report": state["live_next_target_report"],
        "live_next_target_outcome": state["live_next_target_outcome"],
        "current_live_target_outcome": state["live_next_target_outcome"],
        "current_target_outcome": state["live_next_target_outcome"],
        "live_next_target_strict_outcome": state["live_next_target_strict_outcome"],
        "current_live_target_strict_outcome": state["live_next_target_strict_outcome"],
        "current_target_strict_outcome": state["live_next_target_strict_outcome"],
    }
    assert {key: registry[key] for key in alias_values} == alias_values


def test_flattened_current_target_state_has_an_explicit_authority_allowlist() -> None:
    registry = load_registry()
    state = registry["current_target_state"]
    contract = registry["current_target_state_authority_contract_v0"]

    assert contract["schema_id"] == CURRENT_STATE_AUTHORITY_CONTRACT_SCHEMA_ID
    assert contract["authoritative_keys"] == CURRENT_STATE_AUTHORITY_KEYS
    assert set(CURRENT_STATE_AUTHORITY_KEYS) <= set(state)
    assert contract["flattened_compatibility_key_count"] == (
        len(state) - len(CURRENT_STATE_AUTHORITY_KEYS)
    )
    assert "must not override" in contract["authority_rule"]


def test_historical_duplicate_workstream_id_is_quarantined_and_noncurrent() -> None:
    registry = load_registry()
    quarantine = registry["duplicate_workstream_id_quarantine_v0"]
    assert quarantine["collision_count"] == len(quarantine["collisions"]) == 1
    collision = quarantine["collisions"][0]
    assert collision["occurrence_count"] == len(collision["records"]) == 2
    assert collision["legacy_workstream_id"] != registry["current_projection_v0"][
        "current_target"
    ]
    stable_ids = [row["stable_record_id"] for row in collision["records"]]
    assert len(stable_ids) == len(set(stable_ids))
    assert "Use stable_record_id" in quarantine["authority_rule"]


def test_registry_has_no_casefold_key_collisions() -> None:
    registry = load_registry()
    assert casefold_collisions(registry) == []
    aliases = registry["casefold_key_aliases_v0"]
    assert aliases
    assert all(row["canonical_key"].casefold() == row["deprecated_key"].casefold() for row in aliases)
    assert all(
        row["canonical_key"]
        == CANONICAL_CASEFOLD_KEYS[row["canonical_key"].casefold()]
        for row in aliases
    )


def test_registry_integrity_check_accepts_the_canonical_structure() -> None:
    registry = load_registry()
    validate_registry(registry)


def test_legacy_flat_packet_fields_are_explicitly_non_authorizing() -> None:
    registry = load_registry()
    legacy = registry["legacy_flattened_packet_metadata_v0"]
    assert legacy["status"] == "deprecated_non_authorizing_retained_for_compatibility"
    assert "do not override" in legacy["authority_rule"]
