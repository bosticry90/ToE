from __future__ import annotations

import json
import hashlib
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"


def _read(name: str) -> dict:
    return json.loads((RELEASE_ROOT / name).read_text(encoding="utf-8"))


def _sha256(relative_path: str) -> str:
    return hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()


def test_certificate_status_correction_authority_is_nonadvancing() -> None:
    packet = _read(
        "QUADRATIC_STAGE_1_2_CERTIFICATE_STATUS_CORRECTION_AUTHORITY_PACKET_20260729_v0.json"
    )
    review = _read(
        "QUADRATIC_STAGE_1_2_CERTIFICATE_STATUS_CORRECTION_AUTHORITY_PACKET_REVIEW_20260729_v0.json"
    )
    assert packet["status"] == (
        "AUTHORIZED_NONADVANCING_SCIENTIFIC_CUSTODY_CORRECTION_ONLY"
    )
    assert review["status"] == (
        "ACCEPTED_NONADVANCING_SCIENTIFIC_CUSTODY_CORRECTION_AUTHORITY"
    )
    assert packet["scientific_target_preserved"] == (
        "close_toe_native_surrogate_v0_after_bounded_result_v0"
    )
    assert review["scientific_target_preserved"] == packet["scientific_target_preserved"]
    assert packet["preserved_terminal_outcomes"] == {
        "native_surrogate_v0": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "quadratic_control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        "quadratic_toe_role": "REFERENCE_CONTROL_ONLY",
    }
    prohibitions = "\n".join(packet["prohibitions"])
    assert "No reopening" in prohibitions
    assert "No new bounded-program attempt or repair." in prohibitions
    assert "No executable rewrite-confluence proof." in prohibitions
    assert "No new tensor-identity proof." in prohibitions


def test_certificate_addenda_are_hash_bound_and_nonadvancing() -> None:
    stage1 = _read(
        "QFT_GR_QUADRATIC_STAGE_1_REWRITE_CERTIFICATE_STATUS_ADDENDUM_20260729_v0.json"
    )
    stage2 = _read(
        "QFT_GR_QUADRATIC_STAGE_2_ALGEBRAIC_CERTIFICATE_STATUS_ADDENDUM_20260729_v0.json"
    )
    assert stage1["contract_status"] == (
        "GAUGE_ATLAS_AND_JET_CONTRACT_STRUCTURALLY_PRESERVED"
    )
    assert stage1["certificate_status"] == (
        "REWRITE_CONFLUENCE_NOT_EXECUTABLY_ESTABLISHED"
    )
    assert stage2["structural_status"] == (
        "GENERIC_COMPONENT_DAG_STRUCTURALLY_COMPLETE"
    )
    assert stage2["certificate_status"] == "ALGEBRAIC_CERTIFICATION_INCOMPLETE"
    for addendum in (stage1, stage2):
        for artifact in addendum["original_artifacts_preserved"]:
            assert _sha256(artifact["path"]) == artifact["sha256"]
        assert addendum["preserved_terminal_boundaries"] == {
            "bounded_stage_reopened": False,
            "control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
            "missing_proof_added": False,
            "toe_role": "REFERENCE_CONTROL_ONLY",
        }


def test_dependency_index_and_registry_projection_match_addenda() -> None:
    index = _read("QFT_GR_QUADRATIC_CERTIFICATION_STATUS_INDEX_20260729_v0.json")
    assert index["status"] == (
        "CURRENT_QUADRATIC_STAGE_1_2_CERTIFICATION_DEPENDENCY_SURFACE"
    )
    for stage in index["stage_certification"]:
        assert _sha256(stage["addendum_path"]) == stage["addendum_sha256"]
    registry = json.loads(
        (RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json").read_text(encoding="utf-8")
    )
    projection = registry["quadratic_stage_1_2_certificate_status_correction_v0"]
    assert _sha256(projection["status_index_path"]) == projection["status_index_sha256"]
    assert projection["bounded_program_reopened"] is False
    assert projection["scientific_target_rotated"] is False
    assert projection["missing_proofs_added"] is False
    assert projection["quadratic_toe_role_preserved"] == "REFERENCE_CONTROL_ONLY"
    assert projection["quadratic_control_result_preserved"] == (
        "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
    )
    assert projection["native_surrogate_terminal_preserved"] == (
        "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
    )


def test_public_status_surfaces_disclose_certificate_qualifications() -> None:
    required = (
        "REWRITE_CONFLUENCE_NOT_EXECUTABLY_ESTABLISHED",
        "ALGEBRAIC_CERTIFICATION_INCOMPLETE",
    )
    paths = (
        "README.md",
        "State_of_the_Theory.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md",
        "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md",
    )
    for relative_path in paths:
        text = (REPO_ROOT / relative_path).read_text(encoding="utf-8")
        if relative_path == "State_of_the_Theory.md":
            assert "executable rewrite confluence has not been" in text
            assert "independently uncertified" in text
        elif relative_path == "README.md":
            assert "rewrite confluence is not executably established" in text
            assert "not independently certified" in text
        else:
            assert all(token in text for token in required)
