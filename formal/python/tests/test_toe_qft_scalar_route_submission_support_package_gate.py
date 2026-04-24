from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_submission_support_package_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

TITLE_ABSTRACT_LOCK_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "TITLE_ABSTRACT_LOCK.md"
SUBMISSION_METADATA_LOCK_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "SUBMISSION_METADATA_LOCK.md"
COVER_LETTER_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "COVER_LETTER_SKELETON.md"
VENUE_PROFILE_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "VENUE_FORMATTING_PROFILE.md"
FIGURE_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "FIGURE_PACKAGE_PLAN.md"
REVIEWER_SUMMARY_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "REVIEWER_FACING_SUMMARY.md"
EXECUTION_BOARD_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "SUBMISSION_EXECUTION_BOARD.md"
UPLOAD_MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "UPLOAD_BUNDLE_MANIFEST.md"
METADATA_JSON_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "metadata.json"
MAIN_TEX_PATH = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.tex"
FIGURES_DIR = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "figures"

LOCKED_TITLE = "Bounded Free-Scalar QFT-to-QM Bridge: A Governed Canonical Baseline and Low-Energy Extraction"
MAIN_TEX_TITLE = "\\title{Bounded Free-Scalar QFT-to-QM Bridge: \\\\A Governed Canonical Baseline and Low-Energy Extraction}"
LOCKED_ABSTRACT = (
    "We present a bounded free-scalar route that starts from a QFT-first posture and derives a "
    "Schrodinger-class low-energy limit under explicit assumptions. The contribution is governance-first "
    "and reproducibility-first: a pinned derivation and manuscript chain is assembled into one canonical "
    "TeX source with a compile-validated PDF artifact for Paper 1. Claims are intentionally bounded to "
    "free-field structure and interpretive bridge statements; interacting-field, gauge-sector, multi-particle "
    "scattering, and Standard Model completion claims are explicitly out of scope."
)
PLACEHOLDER_EMAIL = "corresponding.author@placeholder.org"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_scalar_submission_support_package_note_has_required_structure() -> None:
    text = _read(NOTE_PATH)
    required_strings = [
        "Support-package components:",
        "Metadata lock coherence:",
        "Support-file bundle completeness:",
        "Figure bundle presence:",
        "Placeholder-control policy:",
        "Pre-upload blocker registry:",
        "SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_STATUS_v0: READY_WITH_OWNER_CONFIRMATION_PENDING_v0",
    ]
    for marker in required_strings:
        assert marker in text, f"Submission-support package note missing marker: {marker}"


def test_scalar_submission_support_package_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_submission_support_package_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_SUBMISSION_SUPPORT_PACKAGE"
    assert artifact.get("scope") == "bounded_free_scalar_paper1_submission_support_bundle"

    checks = artifact.get("support_package_checks", {})
    assert checks.get("metadata_lock_coherence") is True
    assert checks.get("support_file_bundle_complete") is True
    assert checks.get("figure_bundle_present") is True
    assert checks.get("placeholder_control_policy_explicit") is True
    assert checks.get("pre_upload_blocker_registry_pinned") is True

    blockers = artifact.get("owner_confirmation_blockers", {})
    assert blockers.get("corresponding_contact_placeholder_pending") is True
    assert blockers.get("final_upload_bundle_assembly_pending") is True
    assert blockers.get("pending_owner_confirmation_item_count") == 1

    policy = artifact.get("policy_guardrails", {})
    assert policy.get("scalar_paper1_baseline_freeze") is True
    assert policy.get("no_new_scalar_tranche_authorized") is True
    assert policy.get("seam_expansion_held") is True
    assert policy.get("seam_hold_token") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"

    assert artifact.get("status_token") == "SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_STATUS_v0: READY_WITH_OWNER_CONFIRMATION_PENDING_v0"
    assert artifact.get("status") == "READY_WITH_OWNER_CONFIRMATION_PENDING_v0"


def test_scalar_submission_support_package_support_files_are_consistent() -> None:
    title_lock = _read(TITLE_ABSTRACT_LOCK_PATH)
    metadata_lock = _read(SUBMISSION_METADATA_LOCK_PATH)
    cover_letter = _read(COVER_LETTER_PATH)
    venue_profile = _read(VENUE_PROFILE_PATH)
    figure_plan = _read(FIGURE_PLAN_PATH)
    reviewer_summary = _read(REVIEWER_SUMMARY_PATH)
    execution_board = _read(EXECUTION_BOARD_PATH)
    upload_manifest = _read(UPLOAD_MANIFEST_PATH)
    main_tex = _read(MAIN_TEX_PATH)
    metadata = _read_json(METADATA_JSON_PATH)

    for text in (title_lock, metadata_lock):
        assert LOCKED_TITLE in text
    assert MAIN_TEX_TITLE in main_tex
    for text in (title_lock, metadata_lock, main_tex):
        assert LOCKED_ABSTRACT in text

    assert metadata.get("locked_title") == LOCKED_TITLE
    assert metadata.get("locked_abstract") == LOCKED_ABSTRACT
    assert metadata.get("submission_target_primary") == "arXiv"
    assert metadata.get("seam_hold_token") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"

    authors = metadata.get("authors", [])
    assert len(authors) == 1
    assert authors[0].get("name") == "ToE Collaboration"
    assert authors[0].get("affiliation") == "Independent Research Program"
    assert authors[0].get("email") == PLACEHOLDER_EMAIL

    for text in (title_lock, metadata_lock, cover_letter):
        assert PLACEHOLDER_EMAIL in text
    assert "Replace corresponding-contact placeholder with final submission email." in title_lock
    assert "Replace corresponding-contact placeholder with final submission email." in metadata_lock
    assert "Replace corresponding-contact placeholder email with final address." in execution_board
    assert "Corresponding-contact email remains final-owner confirmation item." in upload_manifest

    assert "Title and abstract lock: COMPLETE" in execution_board
    assert "Upload bundle final assembly: IN_PROGRESS" in execution_board
    assert "Primary packaging target:" in venue_profile
    assert "What is not claimed:" in reviewer_summary
    assert "Current production status:" in figure_plan


def test_scalar_submission_support_package_manifest_and_figures_are_present() -> None:
    upload_manifest = _read(UPLOAD_MANIFEST_PATH)
    main_tex = _read(MAIN_TEX_PATH)

    required_files = [
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.tex",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "refs.bib",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "metadata.json",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.pdf",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "main.log",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "TITLE_ABSTRACT_LOCK.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "VENUE_FORMATTING_PROFILE.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "FIGURE_PACKAGE_PLAN.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "COVER_LETTER_SKELETON.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "REVIEWER_FACING_SUMMARY.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "UPLOAD_BUNDLE_MANIFEST.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "SUBMISSION_EXECUTION_BOARD.md",
        REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "SUBMISSION_METADATA_LOCK.md",
        FIGURES_DIR / "scalar_route_flow_v1.pdf",
        FIGURES_DIR / "scalar_route_flow_v1.tex",
        FIGURES_DIR / "claim_boundary_map_v1.pdf",
        FIGURES_DIR / "claim_boundary_map_v1.tex",
    ]
    for path in required_files:
        assert path.exists(), f"Submission support package missing required file: {path}"

    assert "figures/scalar_route_flow_v1.pdf" in upload_manifest
    assert "figures/claim_boundary_map_v1.pdf" in upload_manifest
    assert "includegraphics[width=0.9\\linewidth]{figures/scalar_route_flow_v1.pdf}" in main_tex
    assert "includegraphics[width=0.9\\linewidth]{figures/claim_boundary_map_v1.pdf}" in main_tex


def test_scalar_submission_support_package_is_mirrored_in_authority_surfaces() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_v0.md",
        "formal/output/toe_qft_scalar_route_submission_support_package_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_submission_support_package_gate.py",
        "SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_STATUS_v0: READY_WITH_OWNER_CONFIRMATION_PENDING_v0",
    ]

    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"State/Inventory missing scalar submission-support ref: {ref}"
        )
        assert ref in roadmap_text, f"Roadmap missing scalar submission-support ref: {ref}"