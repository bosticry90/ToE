from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
CLOSURE_PACKAGE_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md"
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
TRACK_A_SCAFFOLD = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01Mainstream3DSpherical.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def _extract_section(text: str, heading: str) -> str:
    match = re.search(
        rf"^## {re.escape(heading)}\n(?P<body>.*?)(?=^## |\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"Missing section: {heading}"
    return match.group("body")


def test_gr_3d_03_closure_package_doc_is_present_and_tokenized() -> None:
    text = _read(CLOSURE_PACKAGE_DOC)
    for token in [
        "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0",
        "TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN",
        "## Closure Transition Rule (v0 bounded/discrete scope)",
        "## Required Closure-Package Deliverables (Path 2; all required)",
        "Closure adjudication status (machine-checkable; required before status change)",
        "Allowed adjudication values:",
        "`NOT_YET_SATISFIED`",
        "`SATISFIED_v0_DISCRETE`",
        "`ADJUDICATION: <allowed value>`",
        "## Mandatory Failure Triggers",
        "## Missing Closure Deliverables Blocking `SATISFIED_v0_DISCRETE` (v0)",
        "## Adjudication Justification (v0)",
        "`NOT_YET_SATISFIED` rationale:",
        "`SATISFIED_v0_DISCRETE` rationale template",
        "No missing closure deliverables remain for `SATISFIED_v0_DISCRETE`.",
        "gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry",
        "gr01_mainstream3d_point_source_model_discrete_delta_or_shell",
        "gr01_mainstream3d_green_class_partial_surface_token",
        "SphericalOperatorEquationAwayFromSourceAssumptions",
        "operator_equation_3d_away_from_source",
        "radiusBound",
        "radial_index_realized_within_bound",
        "Track A green-class token must be derived from 3D operator-equation posture,",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
        "Current adjudication token (v0):",
        "ADJUDICATION: SATISFIED_v0_DISCRETE",
        "does not by itself promote `TOE-GR-3D-03`.",
    ]:
        assert token in text, f"3D-03 closure-package doc missing token: {token}"


def test_gr_3d_03_closure_package_is_wired_into_roadmap_mainstream_target_and_state() -> None:
    roadmap = _read(ROADMAP_DOC)
    mainstream = _read(MAINSTREAM_TARGET_DOC)
    state = _read(STATE_DOC)

    for token in [
        "TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN",
        "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md",
    ]:
        assert token in roadmap, f"Roadmap missing 3D-03 closure-package token: {token}"
        assert token in mainstream, (
            f"Mainstream 3D target missing 3D-03 closure-package token: {token}"
        )
        assert token in state, f"State inventory missing 3D-03 closure-package token: {token}"


def test_gr_3d_03_closure_package_required_track_b_tokens_exist_in_scaffold() -> None:
    scaffold_text = _read(TRACK_B_SCAFFOLD)
    required_tokens = [
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
    ]
    for token in required_tokens:
        assert token in scaffold_text, (
            "Track B scaffold must include required 3D-03 closure-package token: "
            f"{token}"
        )


def test_gr_3d_03_closure_package_required_track_a_tokens_exist_in_scaffold() -> None:
    scaffold_text = _read(TRACK_A_SCAFFOLD)
    required_tokens = [
        "gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry",
        "gr01_mainstream3d_point_source_model_discrete_delta_or_shell",
        "gr01_mainstream3d_green_class_partial_surface_token",
        "SphericalOperatorEquationAwayFromSourceAssumptions",
        "operator_equation_3d_away_from_source",
        "radiusBound",
        "radial_index_realized_within_bound",
    ]
    for token in required_tokens:
        assert token in scaffold_text, (
            "Track A scaffold must include required 3D-03 closure-package token: "
            f"{token}"
        )


def test_gr_3d_03_closure_package_adjudication_enum_is_singleton_and_controls_state_transition() -> None:
    text = _read(CLOSURE_PACKAGE_DOC)
    state = _read(STATE_DOC)

    adjudications = re.findall(
        r"^\s*-\s*`ADJUDICATION:\s*(NOT_YET_SATISFIED|SATISFIED_v0_DISCRETE)`\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert len(adjudications) == 1, (
        "3D-03 closure package must contain exactly one adjudication token "
        "with an allowed value."
    )

    is_blocked_in_state = bool(
        re.search(r"^\- \[B-BLOCKED\] `TOE-GR-3D-03`:", state, flags=re.MULTILINE)
    )

    if adjudications[0] == "SATISFIED_v0_DISCRETE":
        assert not is_blocked_in_state, (
            "State inventory cannot keep TOE-GR-3D-03 as B-BLOCKED after "
            "ADJUDICATION: SATISFIED_v0_DISCRETE is set."
        )
    else:
        assert is_blocked_in_state, (
            "State inventory must keep TOE-GR-3D-03 as B-BLOCKED while "
            "ADJUDICATION: NOT_YET_SATISFIED is set."
        )


def test_gr_3d_03_closure_package_missing_items_and_justification_are_stateful() -> None:
    text = _read(CLOSURE_PACKAGE_DOC)
    missing_items = _extract_section(
        text, "Missing Closure Deliverables Blocking `SATISFIED_v0_DISCRETE` (v0)"
    )
    justification = _extract_section(text, "Adjudication Justification (v0)")

    assert "`NOT_YET_SATISFIED` rationale:" in justification, (
        "Closure package must include explicit NOT_YET_SATISFIED rationale text."
    )
    assert "`SATISFIED_v0_DISCRETE` rationale template" in justification, (
        "Closure package must include a SATISFIED_v0_DISCRETE rationale template."
    )

    adjudications = re.findall(
        r"^\s*-\s*`ADJUDICATION:\s*(NOT_YET_SATISFIED|SATISFIED_v0_DISCRETE)`\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert len(adjudications) == 1, (
        "Closure package must contain exactly one adjudication token before "
        "missing-items state checks."
    )

    open_items = re.findall(r"^\s*-\s*\[ \]\s+", missing_items, flags=re.MULTILINE)
    has_closed_marker = (
        "- [x] No missing closure deliverables remain for `SATISFIED_v0_DISCRETE`."
        in missing_items
    )

    if adjudications[0] == "NOT_YET_SATISFIED":
        assert len(open_items) > 0, (
            "When adjudication is NOT_YET_SATISFIED, missing-items section must "
            "list at least one open blocker."
        )
    else:
        assert len(open_items) == 0, (
            "When adjudication is SATISFIED_v0_DISCRETE, missing-items section "
            "must not list open blockers."
        )
        assert has_closed_marker, (
            "When adjudication is SATISFIED_v0_DISCRETE, missing-items section "
            "must contain the closed marker line."
        )


def test_path2_not_yet_adjudication_requires_track_a_closure_tokens() -> None:
    text = _read(CLOSURE_PACKAGE_DOC)
    mainstream = _read(MAINSTREAM_TARGET_DOC)
    track_a = _read(TRACK_A_SCAFFOLD)

    adjudications = re.findall(
        r"^\s*-\s*`ADJUDICATION:\s*(NOT_YET_SATISFIED|SATISFIED_v0_DISCRETE)`\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert len(adjudications) == 1, "Closure package must contain exactly one adjudication token."
    if adjudications[0] != "NOT_YET_SATISFIED":
        return

    required_tokens = [
        "gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry",
        "gr01_mainstream3d_point_source_model_discrete_delta_or_shell",
        "gr01_mainstream3d_green_class_partial_surface_token",
        "SphericalOperatorEquationAwayFromSourceAssumptions",
        "operator_equation_3d_away_from_source",
        "radiusBound",
        "radial_index_realized_within_bound",
    ]
    for token in required_tokens:
        assert token in mainstream, (
            "Path 2 requires Track A closure token to remain pinned in mainstream target doc: "
            f"{token}"
        )
        assert token in text, (
            "Path 2 requires Track A closure token to remain pinned in closure package doc: "
            f"{token}"
        )
        assert token in track_a, (
            "Path 2 requires Track A closure token to exist in Track A scaffold module: "
            f"{token}"
        )
