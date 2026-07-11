from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_SUBMISSION_READINESS_NOTE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_submission_readiness_checkpoint_v0.json"
CORRECTION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCALAR_ROUTE_SUBMISSION_CHECKPOINT_REFERENTIAL_INTEGRITY_CORRECTION_20260711_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_submission_readiness_note_has_required_structure() -> None:
    text = _read(NOTE_PATH)
    required_strings = [
        "Submission-readiness criteria (bounded):",
        "Final manuscript coherence:",
        "Exact bounded-claim wording:",
        "Section polish:",
        "Terminology consistency:",
        "Internal and external reference consistency:",
        "Submission packaging:",
        "SCALAR_ROUTE_SUBMISSION_READINESS_STATUS_v0: READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE",
    ]
    for marker in required_strings:
        assert marker in text, f"Submission-readiness note missing marker: {marker}"


def test_toe_qft_scalar_submission_readiness_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_submission_readiness_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_SUBMISSION_READINESS"
    assert artifact.get("scope") == "bounded_free_scalar_paper1_submission_assembly"

    criteria = artifact.get("criteria", {})
    assert criteria.get("final_manuscript_coherence") is True
    assert criteria.get("exact_bounded_claim_wording") is True
    assert criteria.get("section_polish_and_transition_consistency") is True
    assert criteria.get("terminology_consistency") is True
    assert criteria.get("internal_external_reference_consistency") is True
    assert criteria.get("submission_packaging_pointer_complete") is True

    correction = _read_json(CORRECTION_PATH)
    corrected = next(
        row
        for row in correction["affected_checkpoints"]
        if row["artifact_id"] == artifact["artifact_id"]
    )
    assert corrected["historical_asserted_value"] is True
    assert corrected["effective_pointer_complete"] is False
    assert corrected["corrected_effective_status"] == (
        "NOT_READY_MISSING_PUBLICATION_CONTRIBUTION_CLASSIFICATION_POINTER_TARGET"
    )

    policy = artifact.get("policy_constraints", {})
    assert policy.get("scalar_paper1_baseline_freeze") is True
    assert policy.get("scalar_extension_policy_exception_only") is True
    assert policy.get("no_new_scalar_tranche_authorized") is True

    assert artifact.get("status_token") == "SCALAR_ROUTE_SUBMISSION_READINESS_STATUS_v0: READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE"
    assert artifact.get("status") == "READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE"


def test_toe_qft_scalar_submission_readiness_is_mirrored_in_authority_surfaces() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_READINESS_NOTE_v0.md",
        "formal/output/toe_qft_scalar_route_submission_readiness_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_submission_readiness_gate.py",
        "SCALAR_ROUTE_SUBMISSION_READINESS_STATUS_v0: READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE",
    ]

    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"State/Inventory missing scalar submission-readiness ref: {ref}"
        )
        assert ref in roadmap_text, f"Roadmap missing scalar submission-readiness ref: {ref}"

    effective_status = (
        "SCALAR_ROUTE_SUBMISSION_EFFECTIVE_READINESS_STATUS_20260711_v0: "
        "NOT_READY_MISSING_PUBLICATION_CONTRIBUTION_CLASSIFICATION_POINTER_TARGET"
    )
    assert effective_status in inventory_text
    assert effective_status in roadmap_text
    assert "Scalar submission lane: NOT_READY_MISSING_PUBLICATION_CONTRIBUTION_CLASSIFICATION_POINTER_TARGET" in state_text
