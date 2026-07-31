from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
RESULT_PATH = (
    RELEASE
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
)
REVIEW_PATH = (
    RELEASE
    / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
)
REGISTRY_PATH = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = (
    "prepare_toe_native_gravitational_requirements_and_candidate_action_"
    "family_survey_bounded_program_v0"
)


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


def test_proposal_freezes_the_exact_ten_by_seven_scope() -> None:
    result = _read(RESULT_PATH)
    assert result["requirement_inventory"] == [
        "R1_DIMENSION",
        "R2_METRIC_ONLY",
        "R3_LOCALITY",
        "R4_DIFF_COVARIANCE",
        "R5_CK_FIREWALL",
        "R6_LOCAL_VARIATION",
        "R7_SOURCE_COMPATIBILITY",
        "R8_NEWTON_POISSON",
        "R9_MOMENTUM_CURRENT",
        "R10_STABILITY_NO_FIT",
    ]
    assert result["candidate_action_family_inventory"] == [
        "F_EH",
        "F_FR",
        "F_QUADRATIC",
        "F_EXTRA_FIELD",
        "F_NONLOCAL",
        "F_CONNECTION_TORSION",
        "F_EQUIVALENCE_PROBE",
    ]
    controls = result["program_controls"]
    assert controls["maximum_native_requirement_rows"] == 10
    assert controls["maximum_action_families"] == 7
    assert controls["maximum_compatibility_cells"] == 70


def test_five_stages_are_bounded_and_nonselecting() -> None:
    result = _read(RESULT_PATH)
    stages = result["stages"]
    assert [stage["stage_number"] for stage in stages] == [1, 2, 3, 4, 5]
    assert [stage["semantic_stage_id"] for stage in stages] == [
        "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY",
        "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY",
        "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION",
        "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY",
        "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF",
    ]
    assert result["program_controls"]["repair_attempt_count"] == 0
    assert result["program_controls"]["no_subsidiary_scientific_targets"] is True
    assert result["closed_lane_boundary"][
        "closed_v2_matrix_population_permitted"
    ] is False
    assert result["closed_lane_boundary"]["v3_automated_tooling_authorized"] is False
    assert "gravitational action adoption" in stages[4]["prohibited_claims"]


def test_proposal_and_review_claim_no_installation_or_action() -> None:
    result = _read(RESULT_PATH)
    boundary = result["nonclaim_boundary"]
    assert result["status"] == (
        "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
    )
    assert all(value is False for value in boundary.values())
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["proposal_only"] is True
    assert review["program_installed"] is False
    assert review["scientific_stage_opened"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["reviewed_result"]["sha256"] == _sha256(RESULT_PATH)


def test_registry_records_preparation_before_later_installation() -> None:
    registry = _read(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    proposed_id = (
        "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_"
        "SURVEY_V0"
    )
    assert projection["current_target"] == TARGET
    assert projection["current_target_outcome"] == (
        "GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_"
        "BOUNDED_PROGRAM_PROPOSAL_PREPARED"
    )
    prepared_registry = json.loads(
        subprocess.run(
            [
                "git",
                "show",
                "f17c85820365dd67ccdde7a5ea53e4879df274b5:"
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
