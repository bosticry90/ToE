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
BASELINE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_SUBMISSION_CANDIDATE_BASELINE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_submission_candidate_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_submission_candidate_baseline_has_required_structure() -> None:
    text = _read(BASELINE_PATH)
    required_strings = [
        "Submission-candidate baseline checks:",
        "Exact bounded claim paragraph:",
        "Physical contribution section readiness:",
        "Terminology consistency across sections:",
        "Section-level classification clarity:",
        "Submission candidate packaging completeness:",
        "SCALAR_ROUTE_SUBMISSION_CANDIDATE_STATUS_v0: BASELINE_LOCKED_FOR_INTERNAL_SUBMISSION_CANDIDATE",
    ]
    for marker in required_strings:
        assert marker in text, f"Submission-candidate baseline missing marker: {marker}"


def test_toe_qft_scalar_submission_candidate_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_submission_candidate_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_SUBMISSION_CANDIDATE_BASELINE"
    assert artifact.get("scope") == "bounded_free_scalar_paper1_internal_submission_candidate"

    checks = artifact.get("submission_candidate_checks", {})
    assert checks.get("exact_bounded_claim_paragraph") is True
    assert checks.get("physical_contribution_section_readiness") is True
    assert checks.get("terminology_consistency_across_sections") is True
    assert checks.get("section_level_classification_clarity") is True
    assert checks.get("submission_candidate_packaging_completeness") is True

    policy = artifact.get("policy_constraints", {})
    assert policy.get("scalar_paper1_baseline_freeze") is True
    assert policy.get("scalar_extension_policy_exception_only") is True
    assert policy.get("no_new_scalar_tranche_authorized") is True

    assert artifact.get("status_token") == "SCALAR_ROUTE_SUBMISSION_CANDIDATE_STATUS_v0: BASELINE_LOCKED_FOR_INTERNAL_SUBMISSION_CANDIDATE"
    assert artifact.get("status") == "BASELINE_LOCKED_FOR_INTERNAL_SUBMISSION_CANDIDATE"


def test_toe_qft_scalar_submission_candidate_is_mirrored_in_authority_surfaces() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_CANDIDATE_BASELINE_v0.md",
        "formal/output/toe_qft_scalar_route_submission_candidate_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_submission_candidate_gate.py",
        "SCALAR_ROUTE_SUBMISSION_CANDIDATE_STATUS_v0: BASELINE_LOCKED_FOR_INTERNAL_SUBMISSION_CANDIDATE",
    ]

    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"State/Inventory missing scalar submission-candidate ref: {ref}"
        )
        assert ref in roadmap_text, f"Roadmap missing scalar submission-candidate ref: {ref}"
