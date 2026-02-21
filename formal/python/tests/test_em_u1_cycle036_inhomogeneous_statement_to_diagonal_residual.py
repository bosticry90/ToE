from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_cycle036_removes_primitive_diagonal_residual_field_from_inhomogeneous_structure() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuityInhomogeneousSourceStatementAssumptions(?P<body>.*?)"
        r"\nstructure MaxwellToContinuitySourceResidualLawAssumptions",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-036 inhomogeneous structure block."
    block = block_match.group("body")
    assert "diagonalResidualLawFromInhomogeneousStatement" not in block, (
        "Cycle-036 must remove primitive `diagonalResidualLawFromInhomogeneousStatement` field."
    )


def test_cycle036_diagonal_residual_theorem_surface_exists_once() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    count = len(
        re.findall(
            r"^theorem\s+em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0\b",
            text,
            flags=re.MULTILINE,
        )
    )
    assert count == 1, (
        "Cycle-036 theorem `em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0` "
        f"must appear exactly once (found {count})."
    )


def test_cycle036_forbids_inline_trivialization_of_diagonal_residual_theorem() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle035_build_source_residual_law_from_inhomogeneous_statement_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-036 diagonal-residual theorem block."
    block = block_match.group("body")
    forbidden_patterns = [r":=\s*by\s*trivial", r":=\s*by\s*simp\b", r":=\s*by\s*aesop\b"]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, block)]
    assert not violations, (
        "Cycle-036 diagonal-residual theorem must not be trivialized by automation. "
        "Forbidden pattern(s): " + ", ".join(violations)
    )


def test_cycle035_mapped_residual_builder_delegates_through_cycle036_theorem() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle035_build_mapped_residual_law_from_inhomogeneous_statement_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-035 mapped-residual builder theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0" in block, (
        "Cycle-035 mapped-residual builder must delegate through the Cycle-036 diagonal-residual theorem."
    )
