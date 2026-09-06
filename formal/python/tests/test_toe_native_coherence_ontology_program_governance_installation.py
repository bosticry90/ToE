from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    COHERENCE_ONTOLOGY_PROGRAM_ID,
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
    / "TOE_NATIVE_COHERENCE_ONTOLOGY_PROGRAM_GOVERNANCE_INSTALLATION_20260729_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_static_manifest_binds_all_five_stages_and_scopes() -> None:
    relative_path = PROGRAM_MANIFEST_PATHS[COHERENCE_ONTOLOGY_PROGRAM_ID]
    manifest = _read(REPO_ROOT / relative_path)
    assert manifest["manifest_mode"] == "PROSPECTIVE_STATIC"
    assert manifest["authorized_stage_count"] == 5
    assert manifest["repair_attempt_count"] == 0
    assert manifest["no_subsidiary_scientific_targets"] is True
    assert manifest["manifest_hash"] == _hashed_payload(manifest, "manifest_hash")
    assert [row["stage_number"] for row in manifest["stages"]] == [1, 2, 3, 4, 5]
    assert len({row["semantic_stage_id"] for row in manifest["stages"]}) == 5
    assert len({row["canonical_target"] for row in manifest["stages"]}) == 5
    for stage in manifest["stages"]:
        assert stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
        assert stage["mandatory_terminal_outcomes"] == (
            stage["canonical_scope"]["terminal_outcome_vocabulary"]
        )


def test_registry_projects_installed_program_as_unopened() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][COHERENCE_ONTOLOGY_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["event_chain_tip_hash"] is None
    assert program["last_closed_attempt_number"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert registry["current_projection_v0"]["current_target"] == (
        "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0"
    )
    assert COHERENCE_ONTOLOGY_PROGRAM_ID in (
        registry[ENFORCEMENT_EXTENSION_KEY]["program_manifests"]
    )
    validate_registry_extension(registry)


def test_installation_artifact_preserves_science_and_does_not_open_stage_1() -> None:
    installation = _read(INSTALLATION_PATH)
    assert installation["status"] == (
        "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION"
    )
    assert installation["installed_program_state"] == "UNOPENED"
    assert installation["stage_1_opened"] is False
    assert installation["scientific_execution_authorized"] is False
    assert installation["repair_attempt_count"] == 0
    assert installation["no_subsidiary_scientific_targets"] is True


def test_installation_result_review_accepts_only_unopened_governance() -> None:
    review = _read(
        RELEASE_ROOT
        / "TOE_NATIVE_COHERENCE_ONTOLOGY_PROGRAM_GOVERNANCE_INSTALLATION_RESULT_REVIEW_20260729_v0.json"
    )
    dependency = _read(
        RELEASE_ROOT
        / "TOE_NATIVE_COHERENCE_STAGE_1_DEPENDENCY_IMPACT_CHECK_20260729_v0.json"
    )
    assert review["accepted"] is True
    assert review["program_state"] == "UNOPENED"
    assert review["stage_1_scientific_output_created"] is False
    assert all(review["checks"].values())
    assert dependency["stage_1_open_permitted_by_dependency_check"] is True
    assert dependency["exhaustive_python_debt"]["exhaustive_passage_established"] is False
    assert dependency["current_dependency_surface_checks"]["scoped_test_count"] == 74
