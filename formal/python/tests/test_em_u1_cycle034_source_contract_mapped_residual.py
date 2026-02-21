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


def test_cycle034_source_contract_surfaces_exist() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityInhomogeneousSourceStatementAssumptions",
        "structure MaxwellToContinuitySourceResidualLawAssumptions",
        "inhomogeneousStatement : MaxwellToContinuityInhomogeneousSourceStatementAssumptions d F J",
        "theorem MaxwellToContinuitySourceResidualLawAssumptions.diagonalResidualLawFromSource",
        "theorem em_u1_cycle034_build_mapped_residual_law_from_source_contract_v0",
        "em_u1_cycle034_build_coupling_from_source_contract_v0",
        "theorem em_u1_cycle034_maxwell_implies_continuity_from_source_contract_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-034 source-contract surfaces missing required token(s): " + ", ".join(missing)


def test_cycle034_source_contract_structure_is_not_vacuous() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuitySourceResidualLawAssumptions(?P<body>.*?)"
        r"\ntheorem MaxwellToContinuityCurrentCouplingAssumptions\.divergenceCurrentFromDd",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-034 source-contract structure block."
    block = block_match.group("body")
    assert ":= True" not in block, "Cycle-034 source-contract structure must not collapse to `:= True`."


def test_cycle034_uniqueness_guards_for_structure_and_theorem_surfaces() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert (
        len(re.findall(r"^structure MaxwellToContinuitySourceResidualLawAssumptions\b", text, flags=re.MULTILINE))
        == 1
    ), "Cycle-034 source-contract structure must appear exactly once."

    theorem_names = [
        "em_u1_cycle034_build_mapped_residual_law_from_source_contract_v0",
        "em_u1_cycle034_build_coupling_from_source_contract_v0",
        "em_u1_cycle034_maxwell_implies_continuity_from_source_contract_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^(?:theorem|def)\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-034 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle034_forbids_empty_source_interface_tags_and_inline_trivialization() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    forbidden_patterns = [
        r"rhoCarrierTag\s*:=\s*\"\"",
        r"spatialCurrentCarrierTag\s*:=\s*\"\"",
        r"continuityConstraintTag\s*:=\s*\"\"",
        r"diagonalResidualLawFromSource\s*:=\s*by\s*trivial",
        r"diagonalResidualLawFromSource\s*:=\s*by\s*simp\b",
        r"diagonalResidualLawFromSource\s*:=\s*by\s*aesop\b",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-034 hardening forbids empty source-interface tags and inline trivialization of "
        "`diagonalResidualLawFromSource`. Forbidden pattern(s): " + ", ".join(violations)
    )


def test_cycle034_mapped_residual_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle034_build_mapped_residual_law_from_source_contract_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(hSourceLaw : MaxwellToContinuitySourceResidualLawAssumptions d F J\)\s*"
        r":\s*\n\s*∀ μ,"
        r"\n\s*continuityResidual d J μ ="
        r"\n\s*ddFromFieldStrength d F μ \(indexConvention\.residualIndexMap μ\)\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-034 mapped-residual theorem signature must remain exact."
    )


def test_cycle034_coupling_builder_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"(?:theorem|def) em_u1_cycle034_build_coupling_from_source_contract_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(hSourceLaw : MaxwellToContinuitySourceResidualLawAssumptions d F J\)\s*"
        r":\s*\n\s*MaxwellToContinuityCurrentCouplingAssumptions d F J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-034 coupling-builder theorem signature must remain exact."
    )


def test_cycle034_maxwell_implies_continuity_delegates_to_cycle032() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle034_maxwell_implies_continuity_from_source_contract_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-034 Maxwell->continuity theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle034_build_coupling_from_source_contract_v0" in block, (
        "Cycle-034 Maxwell->continuity theorem must build coupling through Cycle-034 source-contract surface."
    )
    assert "em_u1_cycle032_maxwell_implies_continuity_for_current_v0" in block, (
        "Cycle-034 Maxwell->continuity theorem must delegate to Cycle-032 surface."
    )
