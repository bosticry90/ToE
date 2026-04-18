from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
PACKAGE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_SUBMISSION_PACKAGE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_submission_package_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_submission_package_doc_has_required_structure() -> None:
    text = _read(PACKAGE_PATH)
    required_strings = [
        "Submission-package components:",
        "Venue and fit note:",
        "Abstract polish lock:",
        "Figure and diagram package lock:",
        "Reviewer-facing bounded-claim summary:",
        "Cover-letter skeleton readiness:",
        "Formatting and metadata readiness:",
        "Policy guardrails:",
        "SCALAR_ROUTE_SUBMISSION_PACKAGE_STATUS_v0: EXTERNAL_SUBMISSION_PACKAGE_READY_BOUNDED",
    ]
    for marker in required_strings:
        assert marker in text, f"Submission package document missing marker: {marker}"


def test_toe_qft_scalar_submission_package_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_submission_package_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_EXTERNAL_SUBMISSION_PACKAGE"
    assert artifact.get("scope") == "bounded_free_scalar_paper1_external_submission_package"

    components = artifact.get("submission_package_components", {})
    assert components.get("venue_fit_note_ready") is True
    assert components.get("abstract_polish_lock_ready") is True
    assert components.get("figure_diagram_package_ready") is True
    assert components.get("reviewer_facing_bounded_claim_summary_ready") is True
    assert components.get("cover_letter_skeleton_ready") is True
    assert components.get("formatting_and_metadata_readiness") is True

    guardrails = artifact.get("policy_guardrails", {})
    assert guardrails.get("scalar_paper1_baseline_freeze") is True
    assert guardrails.get("no_new_scalar_tranche_authorized") is True
    assert guardrails.get("seam_expansion_held") is True
    assert guardrails.get("seam_hold_token") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"

    assert artifact.get("status_token") == "SCALAR_ROUTE_SUBMISSION_PACKAGE_STATUS_v0: EXTERNAL_SUBMISSION_PACKAGE_READY_BOUNDED"
    assert artifact.get("status") == "EXTERNAL_SUBMISSION_PACKAGE_READY_BOUNDED"


def test_toe_qft_scalar_submission_package_is_mirrored_in_authority_surfaces() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_PACKAGE_v0.md",
        "formal/output/toe_qft_scalar_route_submission_package_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_submission_package_gate.py",
        "SCALAR_ROUTE_SUBMISSION_PACKAGE_STATUS_v0: EXTERNAL_SUBMISSION_PACKAGE_READY_BOUNDED",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]

    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"State/Inventory missing scalar submission-package ref: {ref}"
        )
        assert ref in roadmap_text, f"Roadmap missing scalar submission-package ref: {ref}"
