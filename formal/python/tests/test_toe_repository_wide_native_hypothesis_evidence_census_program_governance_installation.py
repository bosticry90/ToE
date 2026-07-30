from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    CENSUS_PROGRAM_ID,
    ENFORCEMENT_EXTENSION_KEY,
    PROGRAMS_KEY,
    PROGRAM_MANIFEST_PATHS,
    _hashed_payload,
    scope_hash,
    validate_registry_extension,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"
INSTALLATION_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_PROGRAM_GOVERNANCE_INSTALLATION_20260730_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_static_manifest_binds_prepared_five_stage_program() -> None:
    relative_path = PROGRAM_MANIFEST_PATHS[CENSUS_PROGRAM_ID]
    manifest = _read(REPO_ROOT / relative_path)
    assert manifest["manifest_mode"] == "PROSPECTIVE_STATIC"
    assert manifest["authorized_stage_count"] == 5
    assert manifest["repair_attempt_count"] == 0
    assert manifest["no_subsidiary_scientific_targets"] is True
    assert manifest["manifest_hash"] == _hashed_payload(manifest, "manifest_hash")
    assert [row["stage_number"] for row in manifest["stages"]] == [1, 2, 3, 4, 5]
    assert [row["semantic_stage_id"] for row in manifest["stages"]] == [
        "REPOSITORY_WIDE_SOURCE_CENSUS",
        "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
        "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
        "CURRENT_HYPOTHESIS_RECONCILIATION",
        "NATIVE_FRONTIER_DECISION",
    ]
    assert len({row["canonical_target"] for row in manifest["stages"]}) == 5
    for stage in manifest["stages"]:
        assert stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
        assert stage["mandatory_terminal_outcomes"] == (
            stage["canonical_scope"]["terminal_outcome_vocabulary"]
        )


def test_registry_projects_census_as_installed_and_unopened() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["event_chain_tip_hash"] is None
    assert program["last_closed_attempt_number"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert registry["current_projection_v0"]["current_target"] == (
        "prepare_toe_repository_wide_native_hypothesis_evidence_census_"
        "bounded_program_v0"
    )
    assert CENSUS_PROGRAM_ID in (
        registry[ENFORCEMENT_EXTENSION_KEY]["program_manifests"]
    )
    validate_registry_extension(registry)


def test_installation_preserves_science_and_does_not_open_stage_1() -> None:
    installation = _read(INSTALLATION_PATH)
    assert installation["status"] == (
        "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION"
    )
    assert installation["installed_program_state"] == "UNOPENED"
    assert installation["stage_1_opened"] is False
    assert installation["scientific_execution_authorized"] is False
    assert installation["scientific_output_created"] is False
    assert installation["archive_scientifically_traversed"] is False
    assert installation["canonical_census_index_generated"] is False
    assert installation["repair_attempt_count"] == 0
    assert installation["no_subsidiary_scientific_targets"] is True
