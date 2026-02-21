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


def test_cycle032_structured_coupling_mapping_surface_exists() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityCurrentCouplingAssumptions",
        "residualIndexMap : SpaceTimeIndex → SpaceTimeIndex",
        "residualIndexMapDiagonal : ∀ μ, residualIndexMap μ = μ",
        "divergenceCurrentFromDdMapped",
        "theorem MaxwellToContinuityCurrentCouplingAssumptions.divergenceCurrentFromDd",
        "theorem em_u1_cycle032_coupling_map_diagonalization_v0",
        "theorem em_u1_cycle032_coupling_map_exports_diagonal_residual_v0",
        "theorem em_u1_cycle032_consume_typed_route_object_for_continuity_v0",
        "theorem em_u1_cycle032_maxwell_implies_continuity_for_current_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Cycle-032 coupling-map surfaces missing required token(s): " + ", ".join(missing)


def test_cycle032_coupling_structure_is_not_vacuous() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuityCurrentCouplingAssumptions(?P<body>.*?)"
        r"\ntheorem MaxwellToContinuityCurrentCouplingAssumptions\.divergenceCurrentFromDd",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate coupling-assumptions structure block."
    block = block_match.group("body")
    assert ":= True" not in block, "Coupling-assumption structure must not collapse to vacuous `:= True`."
    assert "divergenceCurrentFromDd :" not in block, (
        "Cycle-032 requires mapped coupling field; direct diagonal field should be derived via theorem."
    )


def test_cycle032_uniqueness_guards_for_mapping_fields_and_theorem_surfaces() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"structure MaxwellToContinuityCurrentCouplingAssumptions(?P<body>.*?)"
        r"\nstructure MaxwellToContinuityResidualIndexConventionAssumptions",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate Cycle-032 coupling structure block for uniqueness checks."
    block = block_match.group("body")
    assert len(re.findall(r"residualIndexMap\s*:\s*SpaceTimeIndex\s*→\s*SpaceTimeIndex", block)) == 1, (
        "Cycle-032 hardening requires exactly one `residualIndexMap` field in coupling structure."
    )
    assert len(re.findall(r"residualIndexMapDiagonal\s*:\s*∀ μ,\s*residualIndexMap μ = μ", block)) == 1, (
        "Cycle-032 hardening requires exactly one `residualIndexMapDiagonal` field in coupling structure."
    )
    assert len(re.findall(r"divergenceCurrentFromDdMapped\s*:", block)) == 1, (
        "Cycle-032 hardening requires exactly one `divergenceCurrentFromDdMapped` field in coupling structure."
    )

    theorem_names = [
        "MaxwellToContinuityCurrentCouplingAssumptions.divergenceCurrentFromDd",
        "em_u1_cycle032_coupling_map_diagonalization_v0",
        "em_u1_cycle032_coupling_map_exports_diagonal_residual_v0",
        "em_u1_cycle032_consume_typed_route_object_for_continuity_v0",
        "em_u1_cycle032_maxwell_implies_continuity_for_current_v0",
    ]
    for theorem_name in theorem_names:
        count = len(re.findall(rf"^theorem\s+{re.escape(theorem_name)}\b", text, flags=re.MULTILINE))
        assert count == 1, f"Cycle-032 theorem `{theorem_name}` must appear exactly once (found {count})."


def test_cycle032_forbids_literal_identity_map_assignment() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    forbidden_patterns = [
        r"residualIndexMap\s*:=\s*fun\s+μ\s*=>\s*μ",
        r"residualIndexMap\s*:=\s*fun\s+\(\s*μ\s*\)\s*=>\s*μ",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-032 coupling hardening forbids literal identity-map assignment; "
        "use explicit convention/coupling witnesses instead. "
        "Forbidden pattern(s): " + ", ".join(violations)
    )


def test_cycle032_consume_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle032_consume_typed_route_object_for_continuity_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(J : CovariantCurrent\)\s*"
        r"\n\s*\(routeObj : MaxwellToContinuityRouteWithDdSubstepAttempt d F\)\s*"
        r"\n\s*\(hCoupling : MaxwellToContinuityCurrentCouplingAssumptions d F J\)\s*"
        r":\s*\n\s*continuityPredicate d J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-032 continuity-consumer theorem signature must remain exact."
    )


def test_cycle032_maxwell_implies_continuity_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle032_maxwell_implies_continuity_for_current_v0\s*"
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
        r"\n\s*\(hCoupling : MaxwellToContinuityCurrentCouplingAssumptions d F J\)\s*"
        r":\s*\n\s*continuityPredicate d J\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-032 Maxwell->continuity theorem signature must remain exact."
    )


def test_cycle032_theorems_delegate_to_cycle031_surfaces() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)

    consume_block_match = re.search(
        r"theorem em_u1_cycle032_consume_typed_route_object_for_continuity_v0(?P<body>.*?)"
        r"\ntheorem em_u1_cycle032_maxwell_implies_continuity_for_current_v0",
        text,
        flags=re.DOTALL,
    )
    assert consume_block_match is not None, "Could not isolate Cycle-032 consume theorem block."
    consume_block = consume_block_match.group("body")
    assert "em_u1_cycle031_consume_typed_route_object_for_continuity_v0" in consume_block, (
        "Cycle-032 consume theorem must delegate to Cycle-031 continuity-consumer surface."
    )

    maxwell_block_match = re.search(
        r"theorem em_u1_cycle032_maxwell_implies_continuity_for_current_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert maxwell_block_match is not None, "Could not isolate Cycle-032 Maxwell->continuity theorem block."
    maxwell_block = maxwell_block_match.group("body")
    assert "em_u1_cycle031_maxwell_implies_continuity_for_current_v0" in maxwell_block, (
        "Cycle-032 Maxwell->continuity theorem must delegate to Cycle-031 surface."
    )
