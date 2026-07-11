from __future__ import annotations

import hashlib
import json

from formal.python.tools.technical_debt_baseline import (
    MAINTENANCE_TARGET,
    OUTPUT_PATH,
    SCIENTIFIC_TARGET,
    build_baseline,
    canonical_json_bytes,
)


def _artifact() -> dict:
    return json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))


def test_technical_debt_baseline_is_deterministic_and_current() -> None:
    expected = canonical_json_bytes(build_baseline())
    assert OUTPUT_PATH.read_bytes() == expected
    assert hashlib.sha256(expected).hexdigest() == hashlib.sha256(
        OUTPUT_PATH.read_bytes()
    ).hexdigest()


def test_technical_debt_counts_and_stable_ids_are_frozen() -> None:
    debt = _artifact()["technical_debt_baselines"]

    assertions = debt["quarantined_assertions"]["assertions"]
    assert debt["quarantined_assertions"]["assertion_count"] == len(assertions) == 197
    assert debt["quarantined_assertions"]["referenced_test_file_count"] == 186
    assert len({row["assertion_id"] for row in assertions}) == 197

    axioms = debt["lean_axioms"]["axioms"]
    assert debt["lean_axioms"]["axiom_count"] == len(axioms) == 59
    assert debt["lean_axioms"]["axiom_file_count"] == 14
    assert debt["lean_axioms"]["blocking_full_pillar_target_count"] == 22
    assert debt["lean_axioms"]["sorry_or_admit_count"] == 0
    assert len({row["declaration_id"] for row in axioms}) == 59

    opaques = debt["lean_opaque_definitions"]["candidates"]
    assert debt["lean_opaque_definitions"]["candidate_count"] == len(opaques) == 46
    assert debt["lean_opaque_definitions"]["candidate_file_count"] == 14
    assert len({row["declaration_id"] for row in opaques}) == 46

    snapshots = debt["tooling_snapshots"]
    assert snapshots["tracked_snapshot_path_count"] == 59
    assert snapshots["unique_blob_count"] == 36
    assert snapshots["duplicate_group_count"] == 14
    assert snapshots["redundant_worktree_bytes"] == 424_292_098
    assert snapshots["tracked_snapshot_bytes"] == 1_040_485_383


def test_technical_debt_baseline_preserves_authority_and_nonaction_boundaries() -> None:
    artifact = _artifact()
    assert artifact["current_scientific_authority"]["current_target"] == SCIENTIFIC_TARGET
    assert artifact["maintenance_program"]["maintenance_target"] == MAINTENANCE_TARGET
    assert artifact["maintenance_program"]["scientific_target_displacement"] is False
    assert artifact["status"] == "FROZEN_INVENTORY_ONLY_NO_REMEDIATION_OR_AUTHORITY_ROTATION"
    assert all(value is False for value in artifact["boundary"].values())
    assert (
        artifact["verification_contract"][
            "off_device_preservation_required_for_current_maintenance_phase"
        ]
        is False
    )


def test_registry_baseline_binds_the_repaired_monolith_without_retiring_it() -> None:
    registry = _artifact()["technical_debt_baselines"]["loop_control_registry"]
    assert registry["schema_id"] == "LOOP_CONTROL_REGISTRY_v0"
    assert registry["size_bytes"] == 52_340_650
    assert registry["sha256"] == "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
    assert registry["active_workstream_count"] == 1
    assert registry["top_level_key_count"] == 4_153
    assert registry["current_target_state_authoritative_key_count"] == 8
    assert registry["current_target_state_compatibility_key_count"] == 3_742
    assert registry["workstream_record_count"] == 539
    assert registry["unique_workstream_id_count"] == 538
    assert registry["duplicate_workstream_id_group_count"] == 1
    assert registry["duplicate_workstream_extra_record_count"] == 1
