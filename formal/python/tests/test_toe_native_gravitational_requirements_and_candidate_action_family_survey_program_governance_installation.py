from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    ENFORCEMENT_EXTENSION_KEY,
    GRAVITATIONAL_SURVEY_PROGRAM_ID,
    PROGRAMS_KEY,
    PROGRAM_MANIFEST_PATHS,
    _hashed_payload,
    scope_hash,
    validate_registry_extension,
)
from formal.python.tools.toe_native_gravitational_survey_program_governance_installation import (
    INSTALLATION_COMMIT_EXACT_PATH_SET,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"
INSTALLATION_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_"
    "SURVEY_PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_manifest_binds_exact_prepared_five_stage_survey() -> None:
    relative_path = PROGRAM_MANIFEST_PATHS[GRAVITATIONAL_SURVEY_PROGRAM_ID]
    manifest = _read(REPO_ROOT / relative_path)
    assert manifest["manifest_mode"] == "PROSPECTIVE_STATIC"
    assert manifest["authorized_stage_count"] == 5
    assert manifest["repair_attempt_count"] == 0
    assert manifest["no_subsidiary_scientific_targets"] is True
    assert manifest["manifest_hash"] == _hashed_payload(manifest, "manifest_hash")
    assert manifest["installation_envelope"]["commit_exact_path_set"] == sorted(
        INSTALLATION_COMMIT_EXACT_PATH_SET
    )
    assert [row["stage_number"] for row in manifest["stages"]] == [1, 2, 3, 4, 5]
    assert [row["semantic_stage_id"] for row in manifest["stages"]] == [
        "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY",
        "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY",
        "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION",
        "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY",
        "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF",
    ]
    assert [row["canonical_target"] for row in manifest["stages"]] == [
        "inventory_toe_native_gravitational_requirements_v0",
        "inventory_toe_candidate_gravitational_action_families_v0",
        "reconstruct_toe_gravitational_requirement_and_action_family_lineages_v0",
        "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0",
        "select_toe_gravitational_action_family_eligibility_handoff_v0",
    ]
    for stage in manifest["stages"]:
        assert stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
        assert stage["mandatory_terminal_outcomes"] == (
            stage["canonical_scope"]["terminal_outcome_vocabulary"]
        )


def test_manifest_freezes_prepared_workload_caps_and_terminal_outcomes() -> None:
    relative_path = PROGRAM_MANIFEST_PATHS[GRAVITATIONAL_SURVEY_PROGRAM_ID]
    manifest = _read(REPO_ROOT / relative_path)
    assert manifest["workload_caps"] == {
        "maximum_action_families": 7,
        "maximum_compatibility_cells": 70,
        "maximum_evidence_references_per_cell": 8,
        "maximum_extracted_evidence_statements": 512,
        "maximum_lineage_components": 32,
        "maximum_native_requirement_rows": 10,
        "maximum_source_artifacts_for_deep_review": 96,
        "maximum_total_bounded_source_excerpt_words": 24000,
        "maximum_unresolved_lineage_relationships": 32,
    }
    assert manifest["program_terminal_outcomes"] == [
        "ONE_OR_MORE_ACTION_FAMILIES_READY_FOR_SELECTION",
        "ALL_CANDIDATES_REQUIRE_ONE_DEFINITION",
        "ALL_CANDIDATES_REQUIRE_ONE_DERIVATION",
        "NO_PRESERVED_CANDIDATE_SATISFIES_NATIVE_REQUIREMENTS",
        "GRAVITATIONAL_REQUIREMENTS_CONFLICT",
        "SOURCE_EVIDENCE_INSUFFICIENT",
    ]


def test_registry_projects_gravitational_survey_as_installed_unopened() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][GRAVITATIONAL_SURVEY_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["event_chain_tip_hash"] is None
    assert program["last_closed_attempt_number"] == 0
    assert program["repair_attempt_count"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert registry["current_projection_v0"]["current_target"] == (
        "prepare_toe_native_gravitational_requirements_and_candidate_action_"
        "family_survey_bounded_program_v0"
    )
    assert GRAVITATIONAL_SURVEY_PROGRAM_ID in (
        registry[ENFORCEMENT_EXTENSION_KEY]["program_manifests"]
    )
    validate_registry_extension(registry)


def test_installation_is_governance_only_and_does_not_open_stage_one() -> None:
    installation = _read(INSTALLATION_PATH)
    assert installation["status"] == (
        "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION"
    )
    assert installation["installed_program_state"] == "UNOPENED"
    assert installation["attempted_stage_count"] == 0
    assert installation["stage_1_opened"] is False
    assert installation["scientific_execution_authorized"] is False
    assert installation["scientific_output_created"] is False
    assert installation["compatibility_cells_created"] == 0
    assert installation["evidence_promoted"] is False
    assert installation["gravitational_action_selected"] is False
    assert installation["native_gravitational_principle_selected"] is False
    assert installation["gravitational_calculation_started"] is False
