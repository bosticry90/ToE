from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_MIGRATION_PHASE3_IMPLEMENTATION_20260419_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md"
SANDBOX_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md"
PROMOTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _matrix_rows(text: str) -> list[list[str]]:
    start_marker = "## Authority owner matrix"
    end_marker = "Interpretation rules:"
    assert start_marker in text, "Missing authority owner matrix section."
    assert end_marker in text, "Missing interpretation rules section."
    section = text.split(start_marker, 1)[1].split(end_marker, 1)[0]
    rows: list[list[str]] = []
    for line in section.splitlines():
        stripped = line.strip()
        if not stripped.startswith("|"):
            continue
        cells = [cell.strip() for cell in stripped.split("|")[1:-1]]
        if not cells or cells[0] in {"authority_surface", "---"}:
            continue
        rows.append(cells)
    return rows


def test_phase3_cutover_files_exist() -> None:
    for path in (DECLARATION_PATH, MATRIX_PATH):
        assert path.exists(), f"Missing required Phase 3 implementation file: {path}"


def test_phase3_declaration_structure() -> None:
    text = _read(DECLARATION_PATH)
    for section in (
        "## Tranche name",
        "## Objective",
        "## Allowed files",
        "## Out of scope",
        "## Acceptance",
        "## Rollback anchor",
        "## Hard stop rule",
        "## Boundary freshness note",
    ):
        assert section in text


def test_authority_matrix_tokens_and_rows_present() -> None:
    text = _read(MATRIX_PATH)
    for token in (
        "SANDBOX_PROMOTION_AUTHORITY_MATRIX_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "SANDBOX_PROMOTION_AUTHORITY_CUTOVER_RULE_v0: SANDBOX_SURFACES_OWN_SANDBOX_OUTPUT_AUTHORITY_PROMOTION_SURFACES_OWN_CANONICAL_MUTATION_AUTHORITY",
        "SANDBOX_PROMOTION_AUTHORITY_FAIL_CLOSED_RULE_v0: MISSING_OWNER_OR_PARITY_OR_GATE_POINTER_BLOCKS_CUTOVER",
        "SANDBOX_PROMOTION_AUTHORITY_MATRIX_ROW_COUNT_v0: 5",
        "SANDBOX_PROMOTION_AUTHORITY_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
    ):
        assert token in text

    rows = _matrix_rows(text)
    assert len(rows) == 5
    expected_surfaces = {
        "sandbox_lane_policy",
        "promotion_lane_policy",
        "canonical_mutation_protocol",
        "post_pilot_decision_surface",
        "authority_cutover_status",
    }
    found_surfaces = {row[0] for row in rows}
    missing = expected_surfaces - found_surfaces
    assert not missing, "Missing authority surface row(s): " + ", ".join(sorted(missing))
    for row in rows:
        assert len(row) == 4
        assert row[3] == "formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py"


def test_lane_policies_bind_to_authority_cutover() -> None:
    sandbox_text = _read(SANDBOX_POLICY_PATH)
    promotion_text = _read(PROMOTION_POLICY_PATH)

    assert "SANDBOX_PHYSICS_LANE_AUTHORITY_OWNER_v0: formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md" in sandbox_text
    assert "SANDBOX_PHYSICS_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md" in sandbox_text

    assert "PROMOTION_GOVERNANCE_LANE_AUTHORITY_OWNER_v0: formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md" in promotion_text
    assert "PROMOTION_GOVERNANCE_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md" in promotion_text
    assert "PROMOTION_GOVERNANCE_LANE_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py" in promotion_text


def test_phase3_cutover_tokens_mirrored_and_fail_closed() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_tokens = (
        "SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
        "SANDBOX_PROMOTION_PHASE3_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_AUTHORITY_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE3_STATUS_v0: OBJECTIVELY_COMPLETE_AUTHORITY_OWNER_MATRIX_AND_FAIL_CLOSED_CUTOVER_GATE_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE5_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDARY_ENFORCEMENT_FAMILY_AND_FAIL_CLOSED_CLOSEOUT_GATE_PINNED",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    )
    for token in required_tokens:
        assert token in state_text
        assert token in roadmap_text