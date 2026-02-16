from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
ATTEMPT_PACKAGE_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md"
)
MAINSTREAM_TARGET_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md"
)
ROADMAP_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_DOC = REPO_ROOT / "State_of_the_Theory.md"
TRACK_B_SCAFFOLD = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01Mainstream3DPointSource.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def test_gr_3d_03_attempt_package_doc_is_present_and_tokenized() -> None:
    text = _read(ATTEMPT_PACKAGE_DOC)
    for token in [
        "DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0",
        "TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN",
        "## Required Attempt Deliverables (All Required Per Cycle)",
        "## Mandatory Failure Triggers",
        "missing promotion hypothesis.",
        "missing promotion mechanism.",
        "missing attempt cycle ID.",
        "missing objective theorem token in scaffold module.",
        "`Discharge path defined = YES` while status remains `B-AWAITING-DISCHARGE-ATTEMPT`.",
        "## v0 Track B Attempt Package Snapshot",
        "`PILLAR-GR / TOE-GR-3D-03 (Track B)`",
        "`TARGET-GR01-3D-POINT-SOURCE-PLAN`",
        "`TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN`",
        "`Cycle-002 (2026-02-14)`",
        "`B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
        "does not promote `TOE-GR-3D-03` by itself.",
    ]:
        assert token in text, f"3D-03 attempt-package doc missing token: {token}"

    stale_snapshot_tokens = [
        "`Cycle-001 (2026-02-14)`",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
    ]
    for stale_token in stale_snapshot_tokens:
        assert stale_token not in text, (
            "3D-03 attempt-package snapshot must not retain stale Cycle-001 objective "
            f"token after Cycle-002 advancement: {stale_token}"
        )


def test_gr_3d_03_attempt_package_is_wired_into_roadmap_mainstream_target_and_state() -> None:
    roadmap = _read(ROADMAP_DOC)
    mainstream = _read(MAINSTREAM_TARGET_DOC)
    state = _read(STATE_DOC)

    for token in [
        "TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN",
        "DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md",
    ]:
        assert token in roadmap, f"Roadmap missing 3D-03 attempt-package token: {token}"
        assert token in mainstream, (
            f"Mainstream 3D target missing 3D-03 attempt-package token: {token}"
        )
        assert token in state, f"State inventory missing 3D-03 attempt-package token: {token}"


def test_gr_3d_03_attempt_package_objective_token_exists_in_track_b_scaffold() -> None:
    scaffold_text = _read(TRACK_B_SCAFFOLD)
    assert (
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility"
        in scaffold_text
    ), (
        "Track B scaffold must include the objective theorem token used by the "
        "3D-03 bounded discharge-attempt package."
    )
