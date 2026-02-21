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


def test_cycle035_inhomogeneous_statement_surfaces_exist() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityInhomogeneousSourceStatementAssumptions",
        "inhomogeneousStatementTag : String",
        "theorem em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0",
        "em_u1_cycle035_build_source_residual_law_from_inhomogeneous_statement_v0",
        "theorem em_u1_cycle035_build_mapped_residual_law_from_inhomogeneous_statement_v0",
        "em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0",
        "theorem em_u1_cycle035_maxwell_implies_continuity_from_inhomogeneous_statement_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-035 inhomogeneous-statement surfaces missing required token(s): " + ", ".join(missing)


def test_cycle035_uniqueness_guards_for_structure_and_theorem_surfaces() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert (
        len(
            re.findall(
                r"^structure MaxwellToContinuityInhomogeneousSourceStatementAssumptions\b",
                text,
                flags=re.MULTILINE,
            )
        )
        == 1
    ), "Cycle-035 inhomogeneous-source structure must appear exactly once."

    theorem_names = [
        "em_u1_cycle035_build_source_residual_law_from_inhomogeneous_statement_v0",
        "em_u1_cycle035_build_mapped_residual_law_from_inhomogeneous_statement_v0",
        "em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0",
        "em_u1_cycle035_maxwell_implies_continuity_from_inhomogeneous_statement_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^(?:theorem|def)\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-035 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle035_structure_and_tag_are_not_vacuous() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuityInhomogeneousSourceStatementAssumptions(?P<body>.*?)"
        r"\nstructure MaxwellToContinuitySourceResidualLawAssumptions",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-035 inhomogeneous-source structure block."
    block = block_match.group("body")
    assert ":= True" not in block, "Cycle-035 inhomogeneous-source structure must not collapse to `:= True`."

    forbidden_patterns = [
        r"inhomogeneousStatementTag\s*:=\s*\"\"",
        r"em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0\s*:=\s*by\s*trivial",
        r"em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0\s*:=\s*by\s*simp\b",
        r"em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0\s*:=\s*by\s*aesop\b",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-035 hardening forbids vacuous inhomogeneous statement tags and primitive diagonal-law fields. "
        "Forbidden pattern(s): " + ", ".join(violations)
    )


def test_cycle035_source_law_export_theorem_is_derived_from_inhomogeneous_statement() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem MaxwellToContinuitySourceResidualLawAssumptions\.diagonalResidualLawFromSource(?P<body>.*?)"
        r"\ntheorem MaxwellToContinuityCurrentCouplingAssumptions\.divergenceCurrentFromDd",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-035 source-law export theorem block."
    block = block_match.group("body")
    assert "em_u1_cycle036_diagonal_residual_law_from_inhomogeneous_statement_v0" in block, (
        "Cycle-035 source-law export theorem must derive via the Cycle-036 inhomogeneous-statement theorem surface."
    )


def test_cycle035_maxwell_implies_continuity_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle035_maxwell_implies_continuity_from_inhomogeneous_statement_v0\s*"
        r"\n\s*\(consumerPkg : MaxwellToContinuityTypedRouteConsumerAttemptPackage\)\s*"
        r"\n\s*\(hConsumer : maxwellToContinuityTypedRouteConsumerAttemptHarness consumerPkg\)\s*"
        r"\n\s*\(routePkg : MaxwellToContinuityRouteClosureAttemptPackage\)\s*"
        r"\n\s*\(subroutePkg : MaxwellToContinuityDdSubrouteCompositionAttemptPackage\)\s*"
        r"\n\s*\(hRoute : maxwellToContinuityRouteClosureAttemptHarness routePkg\)\s*"
        r"\n\s*\(hSubroute : maxwellToContinuityDdSubrouteCompositionAttemptHarness subroutePkg\)\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(hSmooth : DoubleDivergenceSmoothnessLaneAssumptions d F\)\s*"
        r"\n\s*\(hFantisym : ∀ α β, F.component α β = -F.component β α\)\s*"
        r"\n\s*\(indexConvention : MaxwellToContinuityResidualIndexConventionAssumptions\)\s*"
        r"\n\s*\(hInhom\s*:\s*"
        r"\n\s*MaxwellToContinuityInhomogeneousSourceStatementAssumptions d F J\)\s*"
        r":\s*\n\s*continuityPredicate d J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-035 Maxwell->continuity theorem signature must remain exact."
    )


def test_cycle035_theorems_delegate_to_cycle034_and_cycle032_surfaces() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)

    mapped_block_match = re.search(
        r"theorem em_u1_cycle035_build_mapped_residual_law_from_inhomogeneous_statement_v0(?P<body>.*?)"
        r"\n(?:theorem|def) em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0",
        text,
        flags=re.DOTALL,
    )
    assert mapped_block_match is not None, "Could not isolate Cycle-035 mapped-residual theorem block."
    mapped_block = mapped_block_match.group("body")
    assert "em_u1_cycle034_build_mapped_residual_law_from_source_contract_v0" in mapped_block, (
        "Cycle-035 mapped-residual theorem must delegate to Cycle-034 mapped-residual surface."
    )

    maxwell_block_match = re.search(
        r"theorem em_u1_cycle035_maxwell_implies_continuity_from_inhomogeneous_statement_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert maxwell_block_match is not None, "Could not isolate Cycle-035 Maxwell->continuity theorem block."
    maxwell_block = maxwell_block_match.group("body")
    assert "em_u1_cycle035_build_coupling_from_inhomogeneous_statement_v0" in maxwell_block, (
        "Cycle-035 Maxwell->continuity theorem must build coupling through Cycle-035 builder."
    )
    assert "em_u1_cycle032_maxwell_implies_continuity_for_current_v0" in maxwell_block, (
        "Cycle-035 Maxwell->continuity theorem must delegate to Cycle-032 surface."
    )
