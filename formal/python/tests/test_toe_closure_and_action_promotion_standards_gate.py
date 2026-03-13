from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
CLOSURE_STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_CLOSURE_SEMANTICS_STANDARD_v0.md"
ACTION_STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_COMPLETE_V1_PROGRAM_v0.md"
CANDIDATE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"

CLOSURE_STANDARD_REL = "formal/docs/release/TOE_CLOSURE_SEMANTICS_STANDARD_v0.md"
ACTION_STANDARD_REL = "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md"
GATE_REL = "formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_toe_closure_semantics_standard_is_cross_pinned() -> None:
    closure_text = _read(CLOSURE_STANDARD_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    program_text = _read(PROGRAM_PATH)

    for token in (
        "TOE_CLOSURE_SEMANTICS_STANDARD_v0",
        "PHYSICS-CLOSED",
        "GOVERNANCE-CLOSED",
        "MATRIX-CLOSED",
        "TOE_CLOSURE_SEMANTICS_STANDARD_STATUS_v0: CANONICAL_PINNED",
        "TOE_CLOSURE_SEMANTICS_DEFAULT_CLOSED_MEANING_v0: PHYSICS_CLOSED_UNLESS_QUALIFIED",
        "TOE_COMPLETE_V1_INTERPRETATION_v0: BOUNDED_REPO_COMPLETION_NOT_PHYSICS_COMPLETE",
        GATE_REL,
    ):
        assert token in closure_text

    for ref_text in (roadmap_text, state_text, program_text):
        assert CLOSURE_STANDARD_REL in ref_text
        assert GATE_REL in ref_text


def test_toe_canonical_action_promotion_standard_is_cross_pinned() -> None:
    action_text = _read(ACTION_STANDARD_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    candidate_text = _read(CANDIDATE_PATH)
    program_text = _read(PROGRAM_PATH)

    for token in (
        "TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0",
        "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA",
        "ACTION_PROMOTION_CRITERION_01_v0: THEOREM_LINKED_SEAM_CONSTRAINTS_REQUIRED",
        "ACTION_PROMOTION_CRITERION_02_v0: BRIDGE_TO_OPERATOR_TRANSPORT_CLOSURE_REQUIRED",
        "ACTION_PROMOTION_CRITERION_03_v0: REGIME_LIMIT_SYNCHRONIZATION_WITH_DISCRIMINATOR_SURFACES_REQUIRED",
        "ACTION_PROMOTION_CRITERION_04_v0: ANTI_CIRCULARITY_AND_NO_SHORTCUT_GUARDS_REQUIRED",
        "ACTION_PROMOTION_CRITERION_05_v0: ASSUMPTION_MINIMIZATION_AND_BOUNDARY_PINNING_REQUIRED",
        "TOE_CANONICAL_ACTION_PROMOTION_GATE_v0: EXPLICIT_CROSS_SURFACE_PARITY_REQUIRED",
        GATE_REL,
    ):
        assert token in action_text

    for ref_text in (roadmap_text, state_text, program_text, candidate_text):
        assert ACTION_STANDARD_REL in ref_text

    for token in (
        "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA",
        "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT",
    ):
        assert token in candidate_text


def test_toe_complete_program_and_candidate_action_keep_bounded_interpretation() -> None:
    program_text = _read(PROGRAM_PATH)
    candidate_text = _read(CANDIDATE_PATH)
    state_text = _read(STATE_PATH)

    assert "TOE_COMPLETE_V1_INTERPRETATION_v0: BOUNDED_REPO_COMPLETION_NOT_PHYSICS_COMPLETE" in program_text
    assert "Candidate master action pointer (non-canonical): `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`." in state_text
    for token in (
        "working-form artifact only",
        "explicitly non-canonical",
        "Promotion standard pointer:",
    ):
        assert token in candidate_text