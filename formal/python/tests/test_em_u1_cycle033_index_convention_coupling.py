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


def test_cycle033_index_convention_surfaces_exist() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityResidualIndexConventionAssumptions where",
        "residualIndexMap : SpaceTimeIndex → SpaceTimeIndex",
        "residualIndexMapDiagonal : ∀ μ, residualIndexMap μ = μ",
        "conventionTag : String",
        "em_u1_cycle033_build_coupling_from_index_convention_v0",
        "theorem em_u1_cycle033_diagonal_residual_from_index_convention_v0",
        "theorem em_u1_cycle033_maxwell_implies_continuity_from_index_convention_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-033 index-convention surfaces missing required token(s): " + ", ".join(missing)


def test_cycle033_index_convention_structure_is_not_vacuous() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuityResidualIndexConventionAssumptions(?P<body>.*?)"
        r"\ntheorem MaxwellToContinuityCurrentCouplingAssumptions\.divergenceCurrentFromDd",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-033 index-convention structure block."
    block = block_match.group("body")
    assert ":= True" not in block, "Cycle-033 index-convention structure must not collapse to `:= True`."


def test_cycle033_uniqueness_guards_for_structure_and_theorem_surfaces() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert (
        len(re.findall(r"^structure MaxwellToContinuityResidualIndexConventionAssumptions where", text, flags=re.MULTILINE))
        == 1
    ), "Cycle-033 index-convention structure must appear exactly once."

    theorem_names = [
        "em_u1_cycle033_build_coupling_from_index_convention_v0",
        "em_u1_cycle033_diagonal_residual_from_index_convention_v0",
        "em_u1_cycle033_maxwell_implies_continuity_from_index_convention_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^(?:theorem|def)\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-033 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle033_forbids_empty_convention_tag_assignment() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    forbidden_patterns = [
        r"conventionTag\s*:=\s*\"\"",
        r"conventionTag\s*:=\s*String\.empty",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-033 hardening forbids vacuous convention tags. "
        "Forbidden pattern(s): " + ", ".join(violations)
    )


def test_cycle033_build_coupling_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"(?:theorem|def) em_u1_cycle033_build_coupling_from_index_convention_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(hMapped\s*:\s*"
        r"\n\s*∀ μ,"
        r"\n\s*continuityResidual d J μ ="
        r"\n\s*ddFromFieldStrength d F μ \(indexConvention\.residualIndexMap μ\)\)\s*"
        r":\s*\n\s*MaxwellToContinuityCurrentCouplingAssumptions d F J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-033 build-coupling theorem signature must remain exact."
    )


def test_cycle033_diagonal_residual_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle033_diagonal_residual_from_index_convention_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(hMapped\s*:\s*"
        r"\n\s*∀ μ,"
        r"\n\s*continuityResidual d J μ ="
        r"\n\s*ddFromFieldStrength d F μ \(indexConvention\.residualIndexMap μ\)\)\s*"
        r":\s*\n\s*∀ μ, continuityResidual d J μ = ddFromFieldStrength d F μ μ\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-033 diagonal-residual theorem signature must remain exact."
    )


def test_cycle033_maxwell_implies_continuity_theorem_delegates_to_cycle032() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle033_maxwell_implies_continuity_from_index_convention_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-033 Maxwell->continuity theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle033_build_coupling_from_index_convention_v0" in block, (
        "Cycle-033 Maxwell->continuity theorem must build coupling through Cycle-033 convention theorem."
    )
    assert "em_u1_cycle032_maxwell_implies_continuity_for_current_v0" in block, (
        "Cycle-033 Maxwell->continuity theorem must delegate to Cycle-032 Maxwell->continuity theorem."
    )
