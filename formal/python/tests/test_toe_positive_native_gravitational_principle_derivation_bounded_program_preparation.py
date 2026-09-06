from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
RESULT_PATH = (
    RELEASE
    / "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
)
REVIEW_PATH = (
    RELEASE
    / "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
)
REGISTRY_PATH = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_source_bindings_and_authority_hashes_reproduce() -> None:
    result = _read(RESULT_PATH)
    authority = result["authority_binding"]
    for path_key, hash_key in (
        ("authority_path", "authority_sha256"),
        ("review_path", "review_sha256"),
    ):
        assert _sha256(REPO_ROOT / authority[path_key]) == authority[hash_key]
    for source in result["source_bindings"]:
        assert _sha256(REPO_ROOT / source["path"]) == source["sha256"]


def test_program_is_five_stage_zero_repair_and_finite() -> None:
    result = _read(RESULT_PATH)
    stages = result["stages"]
    assert [stage["stage_number"] for stage in stages] == [1, 2, 3, 4, 5]
    assert [stage["semantic_stage_id"] for stage in stages] == [
        "POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY",
        "POSITIVE_PRINCIPLE_AND_EVALUATION_REQUIREMENT_DISTINCTION",
        "POSITIVE_PRINCIPLE_GRAVITATIONAL_CONSTRAINT_POWER_TEST",
        "PERMITTED_GRAVITATIONAL_ACTION_CLASS_DERIVATION",
        "POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_HANDOFF_DECISION",
    ]
    controls = result["program_controls"]
    assert controls["authorized_stage_count_proposed"] == 5
    assert controls["repair_attempt_count"] == 0
    assert controls["no_subsidiary_scientific_targets"] is True
    assert controls["maximum_source_artifacts_for_deep_review"] == 128
    assert controls["maximum_candidate_principle_families"] == 16


def test_program_distinguishes_principle_from_filters_and_action_construction() -> None:
    result = _read(RESULT_PATH)
    vocab = set(result["principle_status_vocabulary"])
    assert "POSITIVE_GENERATIVE_PRINCIPLE_CANDIDATE" in vocab
    assert "EVALUATION_REQUIREMENT_ONLY" in vocab
    assert "KNOWN_PHYSICS_BASELINE" in vocab
    assert "ARCHITECTURAL_FIREWALL_ONLY" in vocab
    assert "action construction or selection" in result["stages"][0]["prohibited_claims"]
    assert "selection or adoption of one concrete gravitational action" in result["stages"][3]["prohibited_claims"]


def test_terminal_outcomes_and_lifecycle_mappings_are_closed() -> None:
    result = _read(RESULT_PATH)
    assert result["program_terminal_outcomes"] == [
        "POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVED",
        "POSITIVE_PRINCIPLE_RECOVERED_ONLY_AS_BOUNDED_POSTULATE",
        "PRINCIPLE_CONSTRAINS_ACTION_CLASS_BUT_NOT_UNIQUELY",
        "EXISTING_NATIVE_ARCHITECTURE_DOES_NOT_SUPPLY_POSITIVE_GRAVITY_PRINCIPLE",
        "GRAVITY_PRINCIPLE_BLOCKED_BY_MISSING_ONTOLOGY_OR_SEAM_INPUT",
    ]
    mapping = result["result_state_mapping"]
    assert set(mapping.values()) == {"PASS", "BLOCKED", "FAILED"}
    for outcome in result["program_terminal_outcomes"]:
        assert outcome in mapping
    assert result["mandatory_exit_target_proposed"] == (
        "close_toe_positive_native_gravitational_principle_derivation_v0_after_bounded_result_v0"
    )


def test_proposal_and_review_claim_no_installation_or_scientific_result() -> None:
    result = _read(RESULT_PATH)
    assert result["status"] == (
        "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
    )
    assert all(value is False for value in result["nonclaim_boundary"].values())
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["proposal_only"] is True
    assert review["program_installed"] is False
    assert review["scientific_stage_opened"] is False
    assert review["scientific_result_claimed"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["reviewed_result"]["sha256"] == _sha256(RESULT_PATH)


def test_registry_records_preparation_before_later_installation() -> None:
    registry = _read(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    proposed_id = "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
    assert projection["current_target"] == TARGET
    assert projection["current_target_outcome"] == (
        "POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PROPOSAL_PREPARED"
    )
    prepared_registry = json.loads(
        subprocess.run(
            [
                "git",
                "show",
                "d33fd6f0940dd97f0212ec69a66b6f5bcf5f7e86:"
                "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
            ],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
    )
    assert proposed_id not in prepared_registry["bounded_programs_v1"]
    assert registry["bounded_programs_v1"][proposed_id]["state"] == "UNOPENED"
    assert registry["bounded_programs_v1"][proposed_id]["events"] == []
