from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    ENFORCEMENT_EXTENSION_KEY,
    POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID,
    PROGRAMS_KEY,
    PROGRAM_MANIFEST_PATHS,
    _hashed_payload,
    scope_hash,
    validate_registry_extension,
)
from formal.python.tools.toe_positive_gravitational_principle_program_governance_installation import (
    INSTALLATION_COMMIT_EXACT_PATH_SET,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"
INSTALLATION_PATH = (
    RELEASE_ROOT
    / "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_"
    "PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_manifest_binds_exact_prepared_five_stage_program() -> None:
    relative_path = PROGRAM_MANIFEST_PATHS[
        POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID
    ]
    manifest = _read(REPO_ROOT / relative_path)
    assert manifest["manifest_mode"] == "PROSPECTIVE_STATIC"
    assert manifest["authorized_stage_count"] == 5
    assert manifest["repair_attempt_count"] == 0
    assert manifest["no_subsidiary_scientific_targets"] is True
    assert manifest["manifest_hash"] == _hashed_payload(manifest, "manifest_hash")
    assert manifest["installation_envelope"]["commit_exact_path_set"] == sorted(
        INSTALLATION_COMMIT_EXACT_PATH_SET
    )
    assert [stage["stage_number"] for stage in manifest["stages"]] == [
        1,
        2,
        3,
        4,
        5,
    ]
    assert [stage["semantic_stage_id"] for stage in manifest["stages"]] == [
        "POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY",
        "POSITIVE_PRINCIPLE_AND_EVALUATION_REQUIREMENT_DISTINCTION",
        "POSITIVE_PRINCIPLE_GRAVITATIONAL_CONSTRAINT_POWER_TEST",
        "PERMITTED_GRAVITATIONAL_ACTION_CLASS_DERIVATION",
        "POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_HANDOFF_DECISION",
    ]
    for stage in manifest["stages"]:
        assert stage["canonical_scope_hash"] == scope_hash(
            stage["canonical_scope"]
        )
        assert stage["mandatory_terminal_outcomes"] == (
            stage["canonical_scope"]["terminal_outcome_vocabulary"]
        )


def test_manifest_freezes_caps_outcomes_and_principle_distinctions() -> None:
    relative_path = PROGRAM_MANIFEST_PATHS[
        POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID
    ]
    manifest = _read(REPO_ROOT / relative_path)
    assert manifest["workload_caps"][
        "maximum_source_artifacts_for_deep_review"
    ] == 128
    assert manifest["workload_caps"][
        "maximum_candidate_principle_families"
    ] == 16
    assert manifest["program_terminal_outcomes"] == [
        "POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVED",
        "POSITIVE_PRINCIPLE_RECOVERED_ONLY_AS_BOUNDED_POSTULATE",
        "PRINCIPLE_CONSTRAINS_ACTION_CLASS_BUT_NOT_UNIQUELY",
        "EXISTING_NATIVE_ARCHITECTURE_DOES_NOT_SUPPLY_POSITIVE_GRAVITY_PRINCIPLE",
        "GRAVITY_PRINCIPLE_BLOCKED_BY_MISSING_ONTOLOGY_OR_SEAM_INPUT",
    ]
    vocab = set(manifest["principle_status_vocabulary"])
    assert "POSITIVE_GENERATIVE_PRINCIPLE_CANDIDATE" in vocab
    assert "EVALUATION_REQUIREMENT_ONLY" in vocab
    assert "KNOWN_PHYSICS_BASELINE" in vocab
    assert "ARCHITECTURAL_FIREWALL_ONLY" in vocab
    assert set(manifest["result_state_mapping"].values()) == {
        "PASS",
        "BLOCKED",
        "FAILED",
    }


def test_registry_projects_program_as_installed_unopened() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][
        POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID
    ]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["event_chain_tip_hash"] is None
    assert program["last_closed_attempt_number"] == 0
    assert program["repair_attempt_count"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert registry["current_projection_v0"]["current_target"] == (
        "prepare_toe_positive_native_gravitational_principle_derivation_"
        "bounded_program_v0"
    )
    assert POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID in (
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
    assert installation["evidence_promoted"] is False
    assert installation["native_gravitational_principle_selected_or_derived"] is False
    assert installation["gravitational_action_constructed_or_selected"] is False
    assert installation["gravitational_calculation_started"] is False
